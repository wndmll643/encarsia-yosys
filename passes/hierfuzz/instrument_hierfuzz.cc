/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  HierFuzz hierarchical coverage instrumentation passes (v6a and v6b).
 *  Equivalent to firrtl2 hier_cov.hierCoverage_v6a / hierCoverage_v6b.
 *
 *  v6a: data input ports (non-control) for input hash + control registers for core hash
 *  v6b: control input ports (mux-feeding) for input hash + control registers for core hash
 *
 *  Copyright (C) 2024  Matej Bölcskei <mboelcskei@ethz.ch>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/mem.h"
#include <algorithm>
#include <set>
#include <map>
#include <vector>
#include <string>
#include <cmath>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// ---------------------------------------------------------------------------
// Parameters — identical for v6a and v6b
// ---------------------------------------------------------------------------
struct HierCovParams {
	int maxInputHashSize = 6;
	int maxCoreHashSize  = 6;
	int submodHashSize   = 6;
	int covSumSize       = 32;
	int maxInputPorts    = 8;
	int maxBitsPerPort   = 8;
	int maxRegBits       = 64;
	int maxCtrlRegWidth  = 20;
	int bucketCount      = 16;
	int bucketWidth      = 8;
	int maxBucketSigBits = 128;
};

enum InputMode { DATA_INPUTS, CONTROL_INPUTS };

struct NamedBit {
	RTLIL::SigBit bit;
	std::string name;
};

// ---------------------------------------------------------------------------
// Utility functions
// ---------------------------------------------------------------------------

// Must match FIRRTL: s.foldLeft(0)((h,c) => (h*31 + c.toInt) & 0x7fffffff)
static int stable_hash(const std::string &s)
{
	int h = 0;
	for (char c : s)
		h = (h * 31 + (int)(unsigned char)c) & 0x7fffffff;
	return h;
}

static int log2ceil(int x)
{
	int v = x - 1, r = 0;
	while (v > 0) { v >>= 1; r++; }
	return r;
}

static bool is_flipflop(RTLIL::Cell *cell)
{
	return cell->type == ID($dff) || cell->type == ID($dffe) ||
	       cell->type == ID($dffsr) || cell->type == ID($dffsre) ||
	       cell->type == ID($adff) || cell->type == ID($sdff) ||
	       cell->type == ID($sdffe) || cell->type == ID($sdffce) ||
	       cell->type == ID($adffe) || cell->type == ID($aldff) ||
	       cell->type == ID($aldffe);
}

static bool find_clock(RTLIL::Module *module, RTLIL::SigSpec &clock)
{
	for (auto cell : module->selected_cells()) {
		if (is_flipflop(cell)) {
			clock = cell->getPort(ID::CLK);
			if (clock.is_wire()) return true;
		}
	}
	return false;
}

// Strip leading '\' from RTLIL identifier for hashing
static std::string strip_id(const std::string &s)
{
	if (!s.empty() && s[0] == '\\')
		return s.substr(1);
	return s;
}

// Get a meaningful name for an FF (from its Q output wire)
static std::string get_ff_name(RTLIL::Cell *ff)
{
	RTLIL::SigSpec q = ff->getPort(ID::Q);
	if (q.is_wire())
		return strip_id(q.as_wire()->name.str());
	// Multi-bit: use first bit's wire name
	for (auto &bit : q)
		if (bit.wire != nullptr)
			return strip_id(bit.wire->name.str());
	return strip_id(ff->name.str());
}

// ---------------------------------------------------------------------------
// Module analysis: find control FFs, control ports, direct-input FFs
// ---------------------------------------------------------------------------
struct ModuleAnalysis {
	std::set<RTLIL::Cell *> allFFs;
	std::set<RTLIL::Cell *> ctrlFFs;
	std::set<RTLIL::Cell *> dirInFFs;
	std::set<RTLIL::IdString> ctrlPortNames;
};

static void find_mux_sources_rec(
	SigMap &sigmap,
	SigSet<RTLIL::Cell *> &sig2driver,
	RTLIL::Module *module,
	std::set<RTLIL::Cell *> &visited,
	std::set<RTLIL::Cell *> &ctrl_ffs,
	std::set<RTLIL::IdString> &ctrl_port_names,
	RTLIL::SigSpec sig)
{
	// Check if any bit of sig is an input port
	for (auto &bit : sig) {
		if (bit.wire != nullptr && bit.wire->port_input) {
			ctrl_port_names.insert(bit.wire->name);
		}
	}

	std::set<RTLIL::Cell *> drivers;
	sig2driver.find(sigmap(sig), drivers);
	for (auto driver : drivers) {
		if (visited.count(driver)) continue;
		visited.insert(driver);
		if (is_flipflop(driver)) {
			ctrl_ffs.insert(driver);
			continue;
		}
		// Recurse through combinational cell inputs
		for (auto &conn : driver->connections()) {
			if (driver->input(conn.first)) {
				find_mux_sources_rec(sigmap, sig2driver, module, visited,
				                     ctrl_ffs, ctrl_port_names, conn.second);
			}
		}
	}
}

// Trace FF's D input backwards to find all terminal sources (ports or FFs)
static void trace_ff_sources_rec(
	SigMap &sigmap,
	SigSet<RTLIL::Cell *> &sig2driver,
	std::set<RTLIL::Cell *> &visited,
	std::set<RTLIL::Cell *> &source_ffs,
	std::set<RTLIL::IdString> &source_ports,
	RTLIL::SigSpec sig)
{
	for (auto &bit : sig) {
		if (bit.wire != nullptr && bit.wire->port_input) {
			source_ports.insert(bit.wire->name);
		}
	}

	std::set<RTLIL::Cell *> drivers;
	sig2driver.find(sigmap(sig), drivers);
	for (auto driver : drivers) {
		if (visited.count(driver)) continue;
		visited.insert(driver);
		if (is_flipflop(driver)) {
			source_ffs.insert(driver);
			continue;
		}
		for (auto &conn : driver->connections()) {
			if (driver->input(conn.first)) {
				trace_ff_sources_rec(sigmap, sig2driver, visited,
				                     source_ffs, source_ports, conn.second);
			}
		}
	}
}

static std::set<RTLIL::Cell *> find_direct_input_ffs(
	SigMap &sigmap,
	SigSet<RTLIL::Cell *> &sig2driver,
	const std::set<RTLIL::Cell *> &ctrl_ffs)
{
	// Pass 1: find FFs whose D-input sources are exclusively input ports
	std::set<RTLIL::Cell *> first_order;
	for (auto ff : ctrl_ffs) {
		RTLIL::SigSpec d = ff->getPort(ID::D);
		std::set<RTLIL::Cell *> visited;
		std::set<RTLIL::Cell *> src_ffs;
		std::set<RTLIL::IdString> src_ports;
		trace_ff_sources_rec(sigmap, sig2driver, visited, src_ffs, src_ports, d);
		// All sources must be ports (no other FFs) to be direct-input
		if (src_ffs.empty() || (src_ffs.size() == 1 && src_ffs.count(ff)))
			first_order.insert(ff);
	}

	// Pass 2: FFs whose sources are ports or first-order dirIn FFs
	std::set<RTLIL::Cell *> result;
	for (auto ff : ctrl_ffs) {
		RTLIL::SigSpec d = ff->getPort(ID::D);
		std::set<RTLIL::Cell *> visited;
		std::set<RTLIL::Cell *> src_ffs;
		std::set<RTLIL::IdString> src_ports;
		trace_ff_sources_rec(sigmap, sig2driver, visited, src_ffs, src_ports, d);
		// Remove self-reference
		src_ffs.erase(ff);
		// All source FFs must be first-order dirIn
		bool all_dir_in = true;
		for (auto src_ff : src_ffs) {
			if (!first_order.count(src_ff)) {
				all_dir_in = false;
				break;
			}
		}
		if (all_dir_in)
			result.insert(ff);
	}
	return result;
}

static ModuleAnalysis analyze_module(RTLIL::Module *module)
{
	ModuleAnalysis result;
	SigMap sigmap(module);
	SigSet<RTLIL::Cell *> sig2driver;

	for (auto cell : module->cells()) {
		for (auto &conn : cell->connections()) {
			if (cell->output(conn.first))
				sig2driver.insert(sigmap(conn.second), cell);
		}
	}

	for (auto cell : module->cells())
		if (is_flipflop(cell))
			result.allFFs.insert(cell);

	std::set<RTLIL::Cell *> visited;
	for (auto cell : module->cells()) {
		if (cell->type == ID($mux) || cell->type == ID($pmux)) {
			RTLIL::SigSpec select = cell->getPort(ID::S);
			find_mux_sources_rec(sigmap, sig2driver, module, visited,
			                     result.ctrlFFs, result.ctrlPortNames, select);
		}
	}

	result.dirInFFs = find_direct_input_ffs(sigmap, sig2driver, result.ctrlFFs);
	return result;
}

// ---------------------------------------------------------------------------
// Bit selection
// ---------------------------------------------------------------------------

static bool is_clock_or_reset(RTLIL::Wire *wire)
{
	std::string name = wire->name.str();
	std::string lower;
	lower.resize(name.size());
	std::transform(name.begin(), name.end(), lower.begin(), ::tolower);
	return lower.find("clock") != std::string::npos ||
	       lower.find("reset") != std::string::npos ||
	       lower.find("clk") != std::string::npos;
}

static std::vector<NamedBit> select_input_bits(
	RTLIL::Module *module,
	const std::set<RTLIL::IdString> &ctrl_port_names,
	const HierCovParams &params,
	InputMode mode)
{
	std::vector<NamedBit> result;
	int port_count = 0;

	// Iterate ports in declaration order
	for (auto &port_name : module->ports) {
		RTLIL::Wire *wire = module->wire(port_name);
		if (!wire || !wire->port_input) continue;
		if (is_clock_or_reset(wire)) continue;
		if (wire->width < 1) continue;

		bool is_ctrl = ctrl_port_names.count(wire->name) > 0;
		if (mode == DATA_INPUTS && is_ctrl) continue;
		if (mode == CONTROL_INPUTS && !is_ctrl) continue;

		if (port_count >= params.maxInputPorts) break;
		port_count++;

		int width = wire->width;
		int bitsToTake = std::min(params.maxBitsPerPort, width);
		int stride = std::max(1, width / bitsToTake);
		int count = 0;
		for (int i = 0; i < width && count < bitsToTake; i += stride, count++) {
			std::string bit_name = strip_id(wire->name.str()) + "[" + std::to_string(i) + "]";
			result.push_back({RTLIL::SigBit(wire, i), bit_name});
		}
	}
	return result;
}

static std::vector<NamedBit> select_control_reg_bits(
	const std::set<RTLIL::Cell *> &ctrl_ffs,
	const std::set<RTLIL::Cell *> &dir_in_ffs,
	const HierCovParams &params)
{
	// Filter: exclude dirIn FFs with width > 3
	std::set<RTLIL::Cell *> filtered_dir_in;
	for (auto ff : dir_in_ffs) {
		if (ff->getPort(ID::Q).size() > 3)
			filtered_dir_in.insert(ff);
	}

	std::vector<NamedBit> result;
	for (auto ff : ctrl_ffs) {
		if (filtered_dir_in.count(ff)) continue;
		int width = ff->getPort(ID::Q).size();
		if (width >= params.maxCtrlRegWidth) continue;

		RTLIL::SigSpec q = ff->getPort(ID::Q);
		std::string ff_name = get_ff_name(ff);
		int stride = std::max(1, width / std::min(width, 8));
		for (int i = 0; i < width; i += stride) {
			std::string bit_name = ff_name + "[" + std::to_string(i) + "]";
			result.push_back({q[i], bit_name});
			if ((int)result.size() >= params.maxRegBits)
				return result;
		}
	}
	return result;
}

// ---------------------------------------------------------------------------
// Hash building
// ---------------------------------------------------------------------------

// XOR-bucket hash: assign bits to buckets via stableHash(name) % width,
// XOR-reduce each bucket, concatenate results (LSB = bucket[0]).
static RTLIL::SigSpec build_hash(
	RTLIL::Module *module,
	const std::vector<NamedBit> &bits,
	int width)
{
	if (width <= 0)
		return RTLIL::SigSpec();

	// Assign bits to buckets
	std::vector<std::vector<RTLIL::SigBit>> buckets(width);
	for (auto &nb : bits) {
		int h = stable_hash(nb.name);
		int idx = ((h % width) + width) % width;
		buckets[idx].push_back(nb.bit);
	}

	// XOR-reduce each bucket
	RTLIL::SigSpec hash_result;
	for (int i = 0; i < width; i++) {
		if (buckets[i].empty()) {
			hash_result.append(RTLIL::State::S0);
		} else if (buckets[i].size() == 1) {
			hash_result.append(buckets[i][0]);
		} else {
			RTLIL::SigSpec bucket_sig;
			for (auto &bit : buckets[i])
				bucket_sig.append(bit);
			RTLIL::Wire *tmp = module->addWire(NEW_ID, 1);
			module->addReduceXor(NEW_ID, bucket_sig, tmp);
			hash_result.append(RTLIL::SigBit(tmp));
		}
	}

	return hash_result;
}

// Fold address to a narrower width via XOR of chunks
static RTLIL::SigSpec xor_fold_addr(
	RTLIL::Module *module,
	RTLIL::SigSpec addr,
	int addrWidth,
	int outWidth)
{
	if (outWidth <= 0) return RTLIL::SigSpec(RTLIL::State::S0);
	if (addrWidth <= outWidth) return addr;

	RTLIL::SigSpec result = addr.extract(0, outWidth);
	for (int lo = outWidth; lo < addrWidth; lo += outWidth) {
		int len = std::min(outWidth, addrWidth - lo);
		RTLIL::SigSpec chunk = addr.extract(lo, len);
		if (chunk.size() < outWidth)
			chunk.append(RTLIL::Const(0, outWidth - chunk.size()));
		RTLIL::Wire *tmp = module->addWire(NEW_ID, outWidth);
		module->addXor(NEW_ID, result, chunk, tmp);
		result = RTLIL::SigSpec(tmp);
	}
	return result;
}

// ---------------------------------------------------------------------------
// Coverage map creation
// ---------------------------------------------------------------------------
static void create_coverage_map(
	RTLIL::Module *module,
	RTLIL::SigSpec &clock,
	RTLIL::SigSpec &addr,
	int addrWidth,
	RTLIL::SigSpec &is_covered)
{
	RTLIL::IdString memid = RTLIL::escape_id(strip_id(module->name.str()) + "_hierCov");
	int mapSize = 1 << addrWidth;
	Mem mem(module, memid, /*width=*/1, /*start_offset=*/0, /*size=*/mapSize);

	MemRd rd;
	rd.removed = false;
	rd.cell = nullptr;
	rd.clk_polarity = false;
	rd.addr = addr;
	rd.data = is_covered;
	rd.init_value = Const(State::Sx, 1);
	rd.arst_value = Const(State::Sx, 1);
	rd.srst_value = Const(State::Sx, 1);
	rd.transparency_mask = std::vector<bool>(1, false);
	rd.collision_x_mask = std::vector<bool>(1, false);
	mem.rd_ports.push_back(std::move(rd));

	MemWr wr;
	wr.removed = false;
	wr.cell = nullptr;
	wr.wide_log2 = 0;
	wr.clk_enable = true;
	wr.clk_polarity = true;
	wr.priority_mask = std::vector<bool>(1, false);
	wr.clk = clock;
	wr.en = State::S1;
	wr.addr = addr;
	wr.data = State::S1;
	mem.wr_ports.push_back(wr);

	mem.emit();
}

// ---------------------------------------------------------------------------
// Add zero-valued output ports (for modules without clock or coverage bits)
// ---------------------------------------------------------------------------
static void add_zero_outputs(RTLIL::Module *module, const HierCovParams &params)
{
	RTLIL::Wire *io_covsum = module->addWire(RTLIL::escape_id("io_hierCovSum"), params.covSumSize);
	io_covsum->port_output = true;
	RTLIL::Wire *io_covhash = module->addWire(RTLIL::escape_id("io_hierCovHash"), params.submodHashSize);
	io_covhash->port_output = true;
	module->connect(io_covsum, RTLIL::Const(0, params.covSumSize));
	module->connect(io_covhash, RTLIL::Const(0, params.submodHashSize));
	// Add io_covSum for DifuzzRTL receptor compatibility
	if (!module->wire(RTLIL::escape_id("io_covSum"))) {
		RTLIL::Wire *io_drtl_covsum = module->addWire(RTLIL::escape_id("io_covSum"), 30);
		io_drtl_covsum->port_output = true;
		module->connect(io_drtl_covsum, RTLIL::Const(0, 30));
	}
	module->fixup_ports();
}

// ---------------------------------------------------------------------------
// Main coverage instrumentation (per module, recursive)
// ---------------------------------------------------------------------------
static void hierfuzz_coverage_module(
	RTLIL::Design *design,
	RTLIL::Module *module,
	const HierCovParams &params,
	InputMode mode,
	const char *attr_name)
{
	if (module->has_attribute(RTLIL::escape_id(attr_name))) return;

	RTLIL::SigSpec clock;
	bool has_clock = find_clock(module, clock);

	ModuleAnalysis analysis = analyze_module(module);

	// Select input bits
	auto inputBits = select_input_bits(module, analysis.ctrlPortNames, params, mode);

	// Select control register bits
	auto regBits = select_control_reg_bits(analysis.ctrlFFs, analysis.dirInFFs, params);

	// Collect child io_hierCovHash bits (recurse into children first)
	// Snapshot cell list to avoid iterator invalidation
	std::vector<RTLIL::Cell *> submod_cells;
	for (auto cell : module->selected_cells())
		if (cell->type.isPublic())
			submod_cells.push_back(cell);

	std::vector<NamedBit> submodBits;
	for (auto cell : submod_cells) {
		RTLIL::Module *submod = design->module(cell->type);
		if (!submod) continue;

		// Recurse into submodule
		hierfuzz_coverage_module(design, submod, params, mode, attr_name);

		// Check if submodule now has io_hierCovHash
		RTLIL::IdString hash_port = RTLIL::escape_id("io_hierCovHash");
		if (std::find(submod->ports.begin(), submod->ports.end(), hash_port) == submod->ports.end())
			continue;

		RTLIL::Wire *child_hash = module->addWire(NEW_ID, params.submodHashSize);
		cell->setPort(hash_port, child_hash);

		std::string cell_name = strip_id(cell->name.str());
		for (int i = 0; i < params.submodHashSize; i++) {
			std::string name = cell_name + ".io_hierCovHash[" + std::to_string(i) + "]";
			submodBits.push_back({RTLIL::SigBit(child_hash, i), name});
		}
	}

	// Merge regBits + submodBits into coreBits
	std::vector<NamedBit> coreBits;
	coreBits.insert(coreBits.end(), regBits.begin(), regBits.end());
	coreBits.insert(coreBits.end(), submodBits.begin(), submodBits.end());

	// Dynamic hash sizes
	int dynInputHash = inputBits.empty() ? 0 : std::min(params.maxInputHashSize, (int)inputBits.size());
	int dynCoreHash  = coreBits.empty()  ? 0 : std::min(params.maxCoreHashSize,  (int)coreBits.size());
	int addrWidth = dynInputHash + dynCoreHash;

	if (!has_clock || addrWidth == 0) {
		add_zero_outputs(module, params);
		module->set_bool_attribute(RTLIL::escape_id(attr_name));
		log("HierFuzz coverage: %s (no clock or no coverage bits, zero outputs)\n", module->name.c_str());
		return;
	}

	// Build hashes
	RTLIL::SigSpec inputHash = build_hash(module, inputBits, dynInputHash);
	RTLIL::SigSpec coreHash  = build_hash(module, coreBits, dynCoreHash);

	// Address = Cat(inputHash, coreHash) — inputHash is MSB
	RTLIL::SigSpec addr;
	if (dynCoreHash > 0) addr.append(coreHash);    // LSB
	if (dynInputHash > 0) addr.append(inputHash);   // MSB

	// Coverage map
	RTLIL::Wire *is_covered_wire = module->addWire(NEW_ID, 1);
	RTLIL::SigSpec is_covered(is_covered_wire);
	create_coverage_map(module, clock, addr, addrWidth, is_covered);

	// newHit = !is_covered
	RTLIL::Wire *new_hit_wire = module->addWire(NEW_ID, 1);
	module->addNot(NEW_ID, is_covered, new_hit_wire);

	// covSum register: increment on new hit
	RTLIL::Wire *cov_sum = module->addWire(NEW_ID, params.covSumSize);
	RTLIL::Wire *next_sum = module->addWire(NEW_ID, params.covSumSize);
	RTLIL::Wire *inc_sum = module->addWire(NEW_ID, params.covSumSize);
	module->addDff(NEW_ID, clock, next_sum, cov_sum);
	module->addAdd(NEW_ID, cov_sum, RTLIL::Const(1, params.covSumSize), inc_sum);
	// Mux: S=is_covered: Y = S ? cov_sum (B) : inc_sum (A)
	module->addMux(NEW_ID, inc_sum, cov_sum, is_covered, next_sum);

	// Bucket registers
	int bucketIdxWidth = log2ceil(params.bucketCount);
	RTLIL::SigSpec bucketIdx = xor_fold_addr(module, addr, addrWidth, bucketIdxWidth);

	std::vector<RTLIL::Wire *> bucket_q(params.bucketCount);
	for (int i = 0; i < params.bucketCount; i++) {
		RTLIL::Wire *q    = module->addWire(NEW_ID, params.bucketWidth);
		RTLIL::Wire *next = module->addWire(NEW_ID, params.bucketWidth);
		RTLIL::Wire *inc  = module->addWire(NEW_ID, params.bucketWidth);
		RTLIL::Wire *is_b = module->addWire(NEW_ID, 1);
		RTLIL::Wire *mux_inner = module->addWire(NEW_ID, params.bucketWidth);

		module->addDff(NEW_ID, clock, next, q);
		module->addAdd(NEW_ID, q, RTLIL::Const(1, params.bucketWidth), inc);
		module->addEq(NEW_ID, bucketIdx, RTLIL::Const(i, bucketIdxWidth), is_b);
		// inner: isBucket ? inc : q
		module->addMux(NEW_ID, q, inc, is_b, mux_inner);
		// outer: newHit ? inner : q
		module->addMux(NEW_ID, q, mux_inner, new_hit_wire, next);

		bucket_q[i] = q;
	}

	// Build covHash from bucket bits
	std::vector<NamedBit> bucketBits;
	std::string mod_name = strip_id(module->name.str());
	for (int i = 0; i < params.bucketCount; i++) {
		int w = params.bucketWidth;
		int stride = std::max(1, w / std::min(w, 8));
		for (int idx = 0; idx < w && (int)bucketBits.size() < params.maxBucketSigBits; idx += stride) {
			std::string name = mod_name + "_covBucket_" + std::to_string(i) + "[" + std::to_string(idx) + "]";
			bucketBits.push_back({RTLIL::SigBit(bucket_q[i], idx), name});
		}
	}
	RTLIL::SigSpec covHash = build_hash(module, bucketBits, params.submodHashSize);

	// Output ports
	RTLIL::Wire *io_covsum = module->addWire(RTLIL::escape_id("io_hierCovSum"), params.covSumSize);
	io_covsum->port_output = true;
	RTLIL::Wire *io_covhash = module->addWire(RTLIL::escape_id("io_hierCovHash"), params.submodHashSize);
	io_covhash->port_output = true;

	// Add io_covSum (30-bit, zero) for compatibility with DifuzzRTL receptors
	if (!module->wire(RTLIL::escape_id("io_covSum"))) {
		RTLIL::Wire *io_drtl_covsum = module->addWire(RTLIL::escape_id("io_covSum"), 30);
		io_drtl_covsum->port_output = true;
		module->connect(io_drtl_covsum, RTLIL::Const(0, 30));
	}

	// Aggregate child covSums: io_hierCovSum = local + sum(children)
	RTLIL::SigSpec current_sum(cov_sum);
	for (auto cell : submod_cells) {
		RTLIL::Module *submod = design->module(cell->type);
		if (!submod) continue;
		RTLIL::IdString sum_port = RTLIL::escape_id("io_hierCovSum");
		if (std::find(submod->ports.begin(), submod->ports.end(), sum_port) == submod->ports.end())
			continue;

		RTLIL::Wire *child_sum = module->addWire(NEW_ID, params.covSumSize);
		cell->setPort(sum_port, child_sum);
		RTLIL::Wire *new_sum = module->addWire(NEW_ID, params.covSumSize);
		module->addAdd(NEW_ID, current_sum, RTLIL::SigSpec(child_sum), new_sum);
		current_sum = RTLIL::SigSpec(new_sum);
	}
	module->connect(io_covsum, current_sum);
	module->connect(io_covhash, covHash);

	module->fixup_ports();
	module->set_bool_attribute(RTLIL::escape_id(attr_name));
	log("HierFuzz coverage: %s (inputHash=%d, coreHash=%d, addrWidth=%d, ctrlFFs=%d, ctrlPorts=%d)\n",
	    module->name.c_str(), dynInputHash, dynCoreHash, addrWidth,
	    (int)analysis.ctrlFFs.size(), (int)analysis.ctrlPortNames.size());
}

// ---------------------------------------------------------------------------
// MetaAssert instrumentation
// ---------------------------------------------------------------------------
static void hierfuzz_assert_module(
	RTLIL::Design *design,
	RTLIL::Module *module,
	const char *attr_name)
{
	if (module->has_attribute(RTLIL::escape_id(attr_name))) return;

	// Skip if metaAssert already exists (e.g. from DifuzzRTL receptor)
	if (module->wire(RTLIL::escape_id("metaAssert"))) {
		module->set_bool_attribute(RTLIL::escape_id(attr_name));
		return;
	}

	RTLIL::Wire *meta_assert_port = module->addWire(RTLIL::escape_id("metaAssert"), 1);
	meta_assert_port->port_output = true;

	RTLIL::SigSpec clock;
	bool has_clock = find_clock(module, clock);

	// Collect assert-fire enables
	// Snapshot cells to avoid iterator invalidation when adding cells
	std::vector<RTLIL::Cell *> assert_cells;
	for (auto cell : module->cells())
		if (cell->type == ID($assert))
			assert_cells.push_back(cell);

	std::vector<RTLIL::SigSpec> stop_enables;
	for (auto cell : assert_cells) {
		RTLIL::Wire *not_a = module->addWire(NEW_ID, 1);
		RTLIL::Wire *stop_en = module->addWire(NEW_ID, 1);
		module->addNot(NEW_ID, cell->getPort(ID::A), not_a);
		module->addAnd(NEW_ID, cell->getPort(ID::EN), RTLIL::SigSpec(not_a), stop_en);
		stop_enables.push_back(stop_en);
	}

	// Collect child metaAssert outputs
	std::vector<RTLIL::Cell *> assert_submod_cells;
	for (auto cell : module->selected_cells())
		if (cell->type.isPublic())
			assert_submod_cells.push_back(cell);

	for (auto cell : assert_submod_cells) {
		RTLIL::Module *submod = design->module(cell->type);
		if (!submod) continue;
		hierfuzz_assert_module(design, submod, attr_name);
		RTLIL::IdString ap = RTLIL::escape_id("metaAssert");
		if (std::find(submod->ports.begin(), submod->ports.end(), ap) == submod->ports.end())
			continue;
		RTLIL::Wire *child_assert = module->addWire(NEW_ID, 1);
		cell->setPort(ap, child_assert);
		stop_enables.push_back(child_assert);
	}

	// OR-reduce
	RTLIL::SigSpec or_result;
	if (stop_enables.empty()) {
		or_result = RTLIL::Const(0, 1);
	} else {
		or_result = stop_enables[0];
		for (size_t i = 1; i < stop_enables.size(); i++) {
			RTLIL::Wire *tmp = module->addWire(NEW_ID, 1);
			module->addOr(NEW_ID, or_result, stop_enables[i], tmp);
			or_result = RTLIL::SigSpec(tmp);
		}
	}

	// Latch in register if clock available
	if (has_clock && !stop_enables.empty()) {
		RTLIL::Wire *assert_q = module->addWire(NEW_ID, 1);
		RTLIL::Wire *assert_d = module->addWire(NEW_ID, 1);
		module->addDff(NEW_ID, clock, assert_d, assert_q);
		module->addOr(NEW_ID, assert_q, or_result, assert_d);
		module->connect(meta_assert_port, assert_q);
	} else {
		module->connect(meta_assert_port, or_result);
	}

	module->fixup_ports();
	module->set_bool_attribute(RTLIL::escape_id(attr_name));
}

// ---------------------------------------------------------------------------
// MetaReset instrumentation
// ---------------------------------------------------------------------------
static void hierfuzz_reset_module(
	RTLIL::Design *design,
	RTLIL::Module *module,
	const char *attr_name)
{
	if (module->has_attribute(RTLIL::escape_id(attr_name))) return;

	// Skip if metaReset already exists (e.g. from DifuzzRTL receptor)
	if (module->wire(RTLIL::escape_id("metaReset"))) {
		module->set_bool_attribute(RTLIL::escape_id(attr_name));
		return;
	}

	RTLIL::Wire *meta_reset = module->addWire(RTLIL::escape_id("metaReset"));
	meta_reset->port_input = true;
	module->fixup_ports();

	// Snapshot cell list to avoid iterator invalidation
	std::vector<RTLIL::Cell *> reset_cells;
	for (auto cell : module->selected_cells())
		reset_cells.push_back(cell);

	// Note: no _halt ports — matches DifuzzRTL's approach for encarsia compatibility.
	// Each module just gets metaReset, propagated to children.
	for (auto cell : reset_cells) {
		if (is_flipflop(cell)) {
			RTLIL::SigSpec old_d = cell->getPort(ID::D);
			cell->unsetPort(ID::D);
			RTLIL::Wire *new_d = module->addWire(NEW_ID, old_d.size());
			cell->setPort(ID::D, new_d);
			module->addMux(NEW_ID, old_d, RTLIL::Const(0, old_d.size()), meta_reset, new_d);
		} else if (cell->type.isPublic()) {
			RTLIL::Module *submod = design->module(cell->type);
			if (!submod) continue;
			hierfuzz_reset_module(design, submod, attr_name);

			RTLIL::IdString mr = RTLIL::escape_id("metaReset");
			if (std::find(submod->ports.begin(), submod->ports.end(), mr) == submod->ports.end())
				continue;

			cell->setPort(mr, meta_reset);
		}
	}

	module->fixup_ports();
	module->set_bool_attribute(RTLIL::escape_id(attr_name));
}

// ---------------------------------------------------------------------------
// Pass registration
// ---------------------------------------------------------------------------
struct HierFuzzInstrumentV6aPass : public Pass {
	HierFuzzInstrumentV6aPass() : Pass("hierfuzz_instrument_v6a",
		"instrument with hierCov v6a (data-input hash + ctrl-reg core hash)") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    hierfuzz_instrument_v6a\n");
		log("\n");
		log("Instrument the design with hierarchical coverage (v6a).\n");
		log("Uses data input ports (non-control) for input hash and control registers\n");
		log("for core hash. Adds io_hierCovSum, io_hierCovHash, metaAssert, metaReset\n");
		log("ports to every module.\n");
		log("\n");
	}
	void execute(std::vector<std::string>, RTLIL::Design *design) override
	{
		HierCovParams params;
		log("Executing HierFuzz v6a instrumentation.\n");

		// Snapshot modules to avoid iterator invalidation
		std::vector<RTLIL::Module *> modules;
		for (auto module : design->selected_modules())
			modules.push_back(module);

		for (auto module : modules)
			hierfuzz_coverage_module(design, module, params, DATA_INPUTS, "hierfuzz_v6a_cov");
		for (auto module : modules)
			hierfuzz_assert_module(design, module, "hierfuzz_v6a_assert");
		for (auto module : modules)
			hierfuzz_reset_module(design, module, "hierfuzz_v6a_reset");
	}
} HierFuzzInstrumentV6aPass;

struct HierFuzzInstrumentV6bPass : public Pass {
	HierFuzzInstrumentV6bPass() : Pass("hierfuzz_instrument_v6b",
		"instrument with hierCov v6b (ctrl-input hash + ctrl-reg core hash)") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    hierfuzz_instrument_v6b\n");
		log("\n");
		log("Instrument the design with hierarchical coverage (v6b).\n");
		log("Uses control input ports (mux-feeding) for input hash and control registers\n");
		log("for core hash. Adds io_hierCovSum, io_hierCovHash, metaAssert, metaReset\n");
		log("ports to every module.\n");
		log("\n");
	}
	void execute(std::vector<std::string>, RTLIL::Design *design) override
	{
		HierCovParams params;
		log("Executing HierFuzz v6b instrumentation.\n");

		for (auto module : design->selected_modules())
			hierfuzz_coverage_module(design, module, params, CONTROL_INPUTS, "hierfuzz_v6b_cov");
		for (auto module : design->selected_modules())
			hierfuzz_assert_module(design, module, "hierfuzz_v6b_assert");
		for (auto module : design->selected_modules())
			hierfuzz_reset_module(design, module, "hierfuzz_v6b_reset");
	}
} HierFuzzInstrumentV6bPass;

// ---------------------------------------------------------------------------
// V7 parameters — dynamic hash sizing, extmodule proxy, raised caps
// ---------------------------------------------------------------------------
struct HierCovV7Params {
	int maxInputHashSize = 10;
	int maxCoreHashSize  = 12;
	int minHashSize      = 4;
	int submodHashSize   = 6;
	int covSumSize       = 32;
	int maxInputPorts    = 8;
	int maxBitsPerPort   = 8;
	int maxRegBits       = 256;
	int maxCtrlRegWidth  = 20;
	int bucketCount      = 16;
	int bucketWidth      = 8;
	int maxBucketSigBits = 128;
	int maxExtModPorts   = 16;
	int maxExtModBitsPerPort = 8;
};

// Dynamic hash width: for small bit counts use numBits directly,
// for large use log2(numBits), clamped to [minSize, maxSize].
static int dynamic_hash_width(int numBits, int minSize, int maxSize)
{
	if (numBits <= 0) return 0;
	if (numBits <= maxSize) return numBits;
	int w = log2ceil(numBits);
	if (w < minSize) w = minSize;
	if (w > maxSize) w = maxSize;
	return w;
}

// Helper: build a HierCovParams from a HierCovV7Params (C++11 compatible)
static HierCovParams v7_to_v6_params(const HierCovV7Params &v7)
{
	HierCovParams p;
	p.maxInputHashSize = v7.maxInputHashSize;
	p.maxCoreHashSize  = v7.maxCoreHashSize;
	p.submodHashSize   = v7.submodHashSize;
	p.covSumSize       = v7.covSumSize;
	p.maxInputPorts    = v7.maxInputPorts;
	p.maxBitsPerPort   = v7.maxBitsPerPort;
	p.maxRegBits       = v7.maxRegBits;
	p.maxCtrlRegWidth  = v7.maxCtrlRegWidth;
	p.bucketCount      = v7.bucketCount;
	p.bucketWidth      = v7.bucketWidth;
	p.maxBucketSigBits = v7.maxBucketSigBits;
	return p;
}

// Check if a module is a blackbox/extmodule (has attribute or has no cells)
static bool is_extmodule(RTLIL::Module *mod)
{
	if (mod->get_blackbox_attribute())
		return true;
	// Also treat empty modules (no cells at all) as extmodules
	for (auto cell : mod->cells()) {
		(void)cell;
		return false;  // has at least one cell
	}
	return true;  // no cells
}

// Collect proxy coverage bits from extmodule instances (input ports only)
static std::vector<NamedBit> collect_extmodule_proxy_bits(
	RTLIL::Design *design,
	RTLIL::Module *module,
	const HierCovV7Params &params)
{
	std::vector<NamedBit> result;
	for (auto cell : module->cells()) {
		if (!cell->type.isPublic()) continue;
		RTLIL::Module *submod = design->module(cell->type);
		if (!submod) continue;
		if (!is_extmodule(submod))
			continue;

		std::string cell_name = strip_id(cell->name.str());
		int port_count = 0;
		for (auto &port_name : submod->ports) {
			RTLIL::Wire *pw = submod->wire(port_name);
			if (!pw || !pw->port_input) continue;
			if (port_count >= params.maxExtModPorts) break;
			port_count++;

			// Get the signal connected to this port on the instance
			RTLIL::SigSpec sig = cell->getPort(port_name);
			int width = sig.size();
			int bitsToTake = std::min(params.maxExtModBitsPerPort, width);
			int stride = std::max(1, width / bitsToTake);
			int count = 0;
			for (int i = 0; i < width && count < bitsToTake; i += stride, count++) {
				NamedBit nb;
				nb.bit = sig[i];
				nb.name = cell_name + "." + strip_id(port_name.str()) + "[" + std::to_string(i) + "]";
				result.push_back(nb);
			}
		}
	}
	return result;
}

// ---------------------------------------------------------------------------
// V7 coverage instrumentation (per module, recursive)
// ---------------------------------------------------------------------------
static void hierfuzz_coverage_module_v7(
	RTLIL::Design *design,
	RTLIL::Module *module,
	const HierCovV7Params &params,
	const char *attr_name)
{
	if (module->has_attribute(RTLIL::escape_id(attr_name))) return;

	RTLIL::SigSpec clock;
	bool has_clock = find_clock(module, clock);

	ModuleAnalysis analysis = analyze_module(module);

	// Convert v7 params to v6 for reuse of select_input_bits / select_control_reg_bits
	HierCovParams compat = v7_to_v6_params(params);

	// V7 uses data inputs (like v6a)
	auto inputBits = select_input_bits(module, analysis.ctrlPortNames, compat, DATA_INPUTS);

	// V7: select control register bits with raised maxRegBits
	auto regBits = select_control_reg_bits(analysis.ctrlFFs, analysis.dirInFFs, compat);

	// Recurse into children and collect io_hierCovHash
	std::vector<RTLIL::Cell *> submod_cells;
	for (auto cell : module->selected_cells())
		if (cell->type.isPublic())
			submod_cells.push_back(cell);

	std::vector<NamedBit> submodBits;
	for (auto cell : submod_cells) {
		RTLIL::Module *submod = design->module(cell->type);
		if (!submod) continue;

		hierfuzz_coverage_module_v7(design, submod, params, attr_name);

		RTLIL::IdString hash_port = RTLIL::escape_id("io_hierCovHash");
		if (std::find(submod->ports.begin(), submod->ports.end(), hash_port) == submod->ports.end())
			continue;

		RTLIL::Wire *child_hash = module->addWire(NEW_ID, params.submodHashSize);
		cell->setPort(hash_port, child_hash);

		std::string cell_name = strip_id(cell->name.str());
		for (int i = 0; i < params.submodHashSize; i++) {
			std::string name = cell_name + ".io_hierCovHash[" + std::to_string(i) + "]";
			submodBits.push_back({RTLIL::SigBit(child_hash, i), name});
		}
	}

	// V7: collect extmodule proxy bits
	auto extBits = collect_extmodule_proxy_bits(design, module, params);

	// Merge regBits + submodBits + extBits into coreBits
	std::vector<NamedBit> coreBits;
	coreBits.insert(coreBits.end(), regBits.begin(), regBits.end());
	coreBits.insert(coreBits.end(), submodBits.begin(), submodBits.end());
	coreBits.insert(coreBits.end(), extBits.begin(), extBits.end());

	// V7: dynamic hash sizes based on actual bit counts
	int dynInputHash = dynamic_hash_width((int)inputBits.size(), params.minHashSize, params.maxInputHashSize);
	int dynCoreHash  = dynamic_hash_width((int)coreBits.size(), params.minHashSize, params.maxCoreHashSize);
	if (inputBits.empty()) dynInputHash = 0;
	if (coreBits.empty()) dynCoreHash = 0;
	int addrWidth = dynInputHash + dynCoreHash;

	if (!has_clock || addrWidth == 0) {
		add_zero_outputs(module, compat);
		module->set_bool_attribute(RTLIL::escape_id(attr_name));
		log("HierFuzz v7 coverage: %s (no clock or no coverage bits, zero outputs)\n", module->name.c_str());
		return;
	}

	// Build hashes
	RTLIL::SigSpec inputHash = build_hash(module, inputBits, dynInputHash);
	RTLIL::SigSpec coreHash  = build_hash(module, coreBits, dynCoreHash);

	// Address = Cat(inputHash, coreHash) — inputHash is MSB
	RTLIL::SigSpec addr;
	if (dynCoreHash > 0) addr.append(coreHash);
	if (dynInputHash > 0) addr.append(inputHash);

	// Coverage map
	RTLIL::Wire *is_covered_wire = module->addWire(NEW_ID, 1);
	RTLIL::SigSpec is_covered(is_covered_wire);
	create_coverage_map(module, clock, addr, addrWidth, is_covered);

	// newHit = !is_covered
	RTLIL::Wire *new_hit_wire = module->addWire(NEW_ID, 1);
	module->addNot(NEW_ID, is_covered, new_hit_wire);

	// covSum register
	RTLIL::Wire *cov_sum = module->addWire(NEW_ID, params.covSumSize);
	RTLIL::Wire *next_sum = module->addWire(NEW_ID, params.covSumSize);
	RTLIL::Wire *inc_sum = module->addWire(NEW_ID, params.covSumSize);
	module->addDff(NEW_ID, clock, next_sum, cov_sum);
	module->addAdd(NEW_ID, cov_sum, RTLIL::Const(1, params.covSumSize), inc_sum);
	module->addMux(NEW_ID, inc_sum, cov_sum, is_covered, next_sum);

	// Bucket registers
	int bucketIdxWidth = log2ceil(params.bucketCount);
	RTLIL::SigSpec bucketIdx = xor_fold_addr(module, addr, addrWidth, bucketIdxWidth);

	std::vector<RTLIL::Wire *> bucket_q(params.bucketCount);
	for (int i = 0; i < params.bucketCount; i++) {
		RTLIL::Wire *q    = module->addWire(NEW_ID, params.bucketWidth);
		RTLIL::Wire *next = module->addWire(NEW_ID, params.bucketWidth);
		RTLIL::Wire *inc  = module->addWire(NEW_ID, params.bucketWidth);
		RTLIL::Wire *is_b = module->addWire(NEW_ID, 1);
		RTLIL::Wire *mux_inner = module->addWire(NEW_ID, params.bucketWidth);

		module->addDff(NEW_ID, clock, next, q);
		module->addAdd(NEW_ID, q, RTLIL::Const(1, params.bucketWidth), inc);
		module->addEq(NEW_ID, bucketIdx, RTLIL::Const(i, bucketIdxWidth), is_b);
		module->addMux(NEW_ID, q, inc, is_b, mux_inner);
		module->addMux(NEW_ID, q, mux_inner, new_hit_wire, next);

		bucket_q[i] = q;
	}

	// Build covHash from bucket bits
	std::vector<NamedBit> bucketBits;
	std::string mod_name = strip_id(module->name.str());
	for (int i = 0; i < params.bucketCount; i++) {
		int w = params.bucketWidth;
		int stride = std::max(1, w / std::min(w, 8));
		for (int idx = 0; idx < w && (int)bucketBits.size() < params.maxBucketSigBits; idx += stride) {
			std::string name = mod_name + "_covBucket_" + std::to_string(i) + "[" + std::to_string(idx) + "]";
			bucketBits.push_back({RTLIL::SigBit(bucket_q[i], idx), name});
		}
	}
	RTLIL::SigSpec covHash = build_hash(module, bucketBits, params.submodHashSize);

	// Output ports
	RTLIL::Wire *io_covsum = module->addWire(RTLIL::escape_id("io_hierCovSum"), params.covSumSize);
	io_covsum->port_output = true;
	RTLIL::Wire *io_covhash = module->addWire(RTLIL::escape_id("io_hierCovHash"), params.submodHashSize);
	io_covhash->port_output = true;

	// io_covSum dummy for DifuzzRTL receptor compatibility
	if (!module->wire(RTLIL::escape_id("io_covSum"))) {
		RTLIL::Wire *io_drtl_covsum = module->addWire(RTLIL::escape_id("io_covSum"), 30);
		io_drtl_covsum->port_output = true;
		module->connect(io_drtl_covsum, RTLIL::Const(0, 30));
	}

	// Aggregate child covSums
	RTLIL::SigSpec current_sum(cov_sum);
	for (auto cell : submod_cells) {
		RTLIL::Module *submod = design->module(cell->type);
		if (!submod) continue;
		RTLIL::IdString sum_port = RTLIL::escape_id("io_hierCovSum");
		if (std::find(submod->ports.begin(), submod->ports.end(), sum_port) == submod->ports.end())
			continue;

		RTLIL::Wire *child_sum = module->addWire(NEW_ID, params.covSumSize);
		cell->setPort(sum_port, child_sum);
		RTLIL::Wire *new_sum = module->addWire(NEW_ID, params.covSumSize);
		module->addAdd(NEW_ID, current_sum, RTLIL::SigSpec(child_sum), new_sum);
		current_sum = RTLIL::SigSpec(new_sum);
	}
	module->connect(io_covsum, current_sum);
	module->connect(io_covhash, covHash);

	module->fixup_ports();
	module->set_bool_attribute(RTLIL::escape_id(attr_name));
	log("HierFuzz v7 coverage: %s (inputHash=%d, coreHash=%d, addrWidth=%d, ctrlFFs=%d, extBits=%d)\n",
	    module->name.c_str(), dynInputHash, dynCoreHash, addrWidth,
	    (int)analysis.ctrlFFs.size(), (int)extBits.size());
}

// ---------------------------------------------------------------------------
// V7 pass registration
// ---------------------------------------------------------------------------
struct HierFuzzInstrumentV7Pass : public Pass {
	HierFuzzInstrumentV7Pass() : Pass("hierfuzz_instrument_v7",
		"instrument with hierCov v7 (dynamic hash, extmod proxy, raised caps)") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    hierfuzz_instrument_v7\n");
		log("\n");
		log("Instrument the design with hierarchical coverage (v7).\n");
		log("Compared to v6a: dynamic hash sizing (log2-based, clamped [4,12]),\n");
		log("raised maxRegBits (256), extmodule proxy coverage via input ports,\n");
		log("and higher maxInputHashSize (10) / maxCoreHashSize (12).\n");
		log("\n");
	}
	void execute(std::vector<std::string>, RTLIL::Design *design) override
	{
		HierCovV7Params params;
		log("Executing HierFuzz v7 instrumentation.\n");

		std::vector<RTLIL::Module *> modules;
		for (auto module : design->selected_modules())
			modules.push_back(module);

		for (auto module : modules)
			hierfuzz_coverage_module_v7(design, module, params, "hierfuzz_v7_cov");
		for (auto module : modules)
			hierfuzz_assert_module(design, module, "hierfuzz_v7_assert");
		for (auto module : modules)
			hierfuzz_reset_module(design, module, "hierfuzz_v7_reset");
	}
} HierFuzzInstrumentV7Pass;

PRIVATE_NAMESPACE_END
