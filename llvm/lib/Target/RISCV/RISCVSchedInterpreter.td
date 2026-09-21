//===-- RISCVSchedInterpreter.td - Interpreter Scheduling --*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// The scheduling model behind the `generic-interpreter` CPUs.
//
// This starts as a copy of RISCVSchedSpacemitX60.td, which is what
// `generic-rv32` and `generic-rv64` use, with every record renamed. It is a
// starting point chosen for being measured rather than for describing anything
// an interpreter does, and any deviation from it belongs in its own change with
// a measurement attached.
//
// The obvious model of an interpreter - a single serial dispatch slot whose
// occupancy is the per-dispatch cost, latency equal to it because a handler
// completes before the next dispatch begins - was tried first and is much
// worse. Occupancy equal to latency leaves a scheduler no slack, so there is no
// gap to fill and no reason to keep a producer near its consumer, while it
// stays free to lengthen a live range for other reasons. On a 5x5-limb field
// multiply from curve25519-dalek that left all fifty partial products live at
// once for 27 spill stores, where this model interleaves each product with its
// consumer and spills nothing; the workload ran 10% slower than with no
// scheduler at all. A spill is a guest memory access, which is among the most
// expensive dispatches an interpreter performs, so a model that trades
// dispatches for spills loses on its own terms.
//
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
//
// Scheduler model for the SpacemiT-X60 processor based on documentation of the
// C908 and experiments on real hardware (bpi-f3).
//
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
// Helpers

// Maps LMUL string to corresponding value from the Values array
// LMUL values map to array indices as follows:
//   MF8 -> Values[0], MF4 -> Values[1], MF2 -> Values[2], M1 -> Values[3],
//   M2 -> Values[4], M4 -> Values[5], M8 -> Values[6]
// Shorter lists are allowed, e.g., widening instructions don't work on M8
class InterpGetLMULValue<list<int> Values, string LMUL> {
  defvar Index = !cond(
    !eq(LMUL, "MF8"): 0,
    !eq(LMUL, "MF4"): 1,
    !eq(LMUL, "MF2"): 2,
    !eq(LMUL, "M1"):  3,
    !eq(LMUL, "M2"):  4,
    !eq(LMUL, "M4"):  5,
    !eq(LMUL, "M8"):  6,
  );

  assert !lt(Index, !size(Values)),
    "Missing LMUL value for '" # LMUL # "'. " #
    "Expected at least " # !add(Index, 1) # " elements, but got " #
    !size(Values) # ".";

  int c = Values[Index];
}

// Returns BaseValue for LMUL values before startLMUL, Value for startLMUL,
// then doubles Value for each subsequent LMUL
// Example: InterpConstValueUntilLMULThenDoubleBase<"M1", 2, 4, "M8"> returns:
//   MF8->2, MF4->2, MF2->2, M1->4, M2->8, M4->16, M8->32
// This is useful for modeling scheduling parameters that scale with LMUL.
class InterpConstValueUntilLMULThenDoubleBase<string startLMUL, int BaseValue, int Value, string currentLMUL> {
  assert !le(BaseValue, Value), "BaseValue must be less-equal to Value";
  defvar startPos = InterpGetLMULValue<[0, 1, 2, 3, 4, 5, 6], startLMUL>.c;
  defvar currentPos = InterpGetLMULValue<[0, 1, 2, 3, 4, 5, 6], currentLMUL>.c;

  // Calculate the difference in positions
  defvar posDiff = !sub(currentPos, startPos);

  // Calculate Value * (2^posDiff)
  int c = !cond(
    !eq(posDiff, 0) : Value,
    !eq(posDiff, 1) : !mul(Value, 2),
    !eq(posDiff, 2) : !mul(Value, 4),
    !eq(posDiff, 3) : !mul(Value, 8),
    !eq(posDiff, 4) : !mul(Value, 16),
    !eq(posDiff, 5) : !mul(Value, 32),
    !eq(posDiff, 6) : !mul(Value, 64),
    true : BaseValue
  );
}

// Same as the previous function but BaseValue == Value
class InterpConstValueUntilLMULThenDouble<string startLMUL, int Value, string currentLMUL> {
  int c = InterpConstValueUntilLMULThenDoubleBase<startLMUL, Value, Value, currentLMUL>.c;
}

// Returns MF8->1, MF4->1, MF2->2, M1->4, M2->8, M4->16, M8->32
class InterpConstOneUntilMF4ThenDouble<string mx> {
  int c = InterpConstValueUntilLMULThenDouble<"MF4", 1, mx>.c;
}

// Returns MF8->1, MF4->1, MF2->1, M1->2, M2->4, M4->8, M8->16
class InterpConstOneUntilMF2ThenDouble<string mx> {
  int c = InterpConstValueUntilLMULThenDouble<"MF2", 1, mx>.c;
}

// Returns MF8->1, MF4->1, MF2->1, M1->1, M2->2, M4->4, M8->8
class InterpConstOneUntilM1ThenDouble<string mx> {
  int c = InterpConstValueUntilLMULThenDouble<"M1", 1, mx>.c;
}

//===----------------------------------------------------------------------===//
// Latency helper classes

// Used for: arithmetic (add/sub/min/max), saturating/averaging, FP add/sub/min/max
class InterpGet4458Latency<string mx> {
  int c = InterpGetLMULValue<[/*MF8=*/4, /*MF4=*/4, /*MF2=*/4, /*M1=*/4, /*M2=*/4, /*M4=*/5, /*M8=*/8], mx>.c;
}

// Used for: widening operations (no M8)
class InterpGet4588Latency<string mx> {
  int c = InterpGetLMULValue<[/*MF8=*/4, /*MF4=*/4, /*MF2=*/4, /*M1=*/4, /*M2=*/5, /*M4=*/8], mx>.c;
}

// Used for: mask-producing comparisons, carry ops with mask, FP comparisons
class InterpGet461018Latency<string mx> {
  int c = InterpGetLMULValue<[/*MF8=*/4, /*MF4=*/4, /*MF2=*/4, /*M1=*/4, /*M2=*/6, /*M4=*/10, /*M8=*/18], mx>.c;
}

// Used for: FP FMA operations, complex FP ops
class InterpGet6678Latency<string mx> {
  int c = InterpGetLMULValue<[/*MF8=*/6, /*MF4=*/6, /*MF2=*/6, /*M1=*/6, /*M2=*/6, /*M4=*/7, /*M8=*/8], mx>.c;
}

//===----------------------------------------------------------------------===//

class InterpIsWorstCaseMX<string mx, list<string> MxList> {
  string LLMUL = LargestLMUL<MxList>.r;
  bit c = !eq(mx, LLMUL);
}

class InterpIsWorstCaseMXSEW<string mx, int sew, list<string> MxList, bit isF = 0> {
  string LLMUL = LargestLMUL<MxList>.r;
  int SSEW = SmallestSEW<mx, isF>.r;
  bit c = !and(!eq(mx, LLMUL), !eq(sew, SSEW));
}

defvar InterpVLEN = 256;
defvar InterpDLEN = !div(InterpVLEN, 2);

class InterpGetLMulCycles<string mx> {
  int c = !cond(
    !eq(mx, "M1") : 1,
    !eq(mx, "M2") : 2,
    !eq(mx, "M4") : 4,
    !eq(mx, "M8") : 8,
    !eq(mx, "MF2") : 1,
    !eq(mx, "MF4") : 1,
    !eq(mx, "MF8") : 1
  );
}

class InterpGetVLMAX<string mx, int sew> {
  defvar LMUL = InterpGetLMulCycles<mx>.c;
  int val = !cond(
    !eq(mx, "MF2") : !div(!div(InterpVLEN, 2), sew),
    !eq(mx, "MF4") : !div(!div(InterpVLEN, 4), sew),
    !eq(mx, "MF8") : !div(!div(InterpVLEN, 8), sew),
    true: !div(!mul(InterpVLEN, LMUL), sew)
  );
}

// Latency for segmented loads and stores are calculated as vl * nf.
class InterpSegmentedLdStCycles<string mx, int sew, int nf> {
  int c = !mul(InterpGetVLMAX<mx, sew>.val, nf);
}

def InterpreterModel : SchedMachineModel {
  let IssueWidth        = 2; // dual-issue
  let MicroOpBufferSize = 0; // in-order
  let LoadLatency       = 3; // worse case: >= 3
  let MispredictPenalty = 9; // nine-stage

  let CompleteModel = 0;

  let UnsupportedFeatures = [HasStdExtZknd, HasStdExtZkne, HasStdExtZknh,
                             HasStdExtZksed, HasStdExtZksh, HasStdExtZkr];
}

let SchedModel = InterpreterModel in {

//===----------------------------------------------------------------------===//
// Define processor resources for Spacemit-X60

// Information gathered from the C908 user manual:
let BufferSize = 0 in {
  // The LSU supports dual issue for scalar store/load instructions
  def Interp_LS : ProcResource<2>;

  // An IEU can decode and issue two instructions at the same time
  def Interp_IEUA : ProcResource<1>;
  def Interp_IEUB : ProcResource<1>;
  def Interp_IEU : ProcResGroup<[Interp_IEUA, Interp_IEUB]>;

  // Although the X60 does appear to support multiple issue for at least some
  // floating point instructions, this model assumes single issue as
  // increasing it reduces the gains we saw in performance
  def Interp_FP : ProcResource<1>;

  // Vector pipeline
  // Single issue for vector store/load instructions
  def Interp_VLS : ProcResource<1>;

  // The C908 user manual says: "Vector floating-point units support vector
  // floating-point computation of different bits. In addition, vector integer
  // units are added". Developer confirmed it's a separate VIEU
  def Interp_VIEU : ProcResource<1>;

  // The C908 user manual says: "The vector execution unit is developed by
  // extending the floating-point unit", so let's assume single issue for now
  def Interp_VFP : ProcResource<1>;
}

//===----------------------------------------------------------------------===//

// Branching
def : WriteRes<WriteJmp, [Interp_IEUA]>;
def : WriteRes<WriteJal, [Interp_IEUA]>;
def : WriteRes<WriteJalr, [Interp_IEUA]>;

// Integer arithmetic and logic
// Latency of ALU instructions is 1, but add.uw is 2
def : WriteRes<WriteIALU32, [Interp_IEU]>;
def : WriteRes<WriteIALU, [Interp_IEU]>;
def : WriteRes<WriteShiftImm32, [Interp_IEU]>;
def : WriteRes<WriteShiftImm, [Interp_IEU]>;
def : WriteRes<WriteShiftReg32, [Interp_IEU]>;
def : WriteRes<WriteShiftReg, [Interp_IEU]>;

// Integer multiplication
def : WriteRes<WriteIMul32, [Interp_IEU]>  { let Latency = 3; }

// The latency of mul is 5, while in mulh, mulhsu, mulhu is 6
// Worst case latency is used
def : WriteRes<WriteIMul, [Interp_IEU]>  { let Latency = 6; }

// Integer division/remainder
// TODO: Latency set based on C908 datasheet and hasn't been
// confirmed experimentally.
let Latency = 12, ReleaseAtCycles = [12] in {
  def : WriteRes<WriteIDiv32, [Interp_IEUA]>;
  def : WriteRes<WriteIRem32, [Interp_IEUA]>;
}
let Latency = 20, ReleaseAtCycles = [20] in {
  def : WriteRes<WriteIDiv, [Interp_IEUA]>;
  def : WriteRes<WriteIRem, [Interp_IEUA]>;
}

// Bitmanip
def : WriteRes<WriteRotateImm, [Interp_IEU]>;
def : WriteRes<WriteRotateImm32, [Interp_IEU]>;
def : WriteRes<WriteRotateReg, [Interp_IEU]>;
def : WriteRes<WriteRotateReg32, [Interp_IEU]>;

def : WriteRes<WriteCLZ, [Interp_IEU]>;
def : WriteRes<WriteCLZ32, [Interp_IEU]>;
def : WriteRes<WriteCTZ, [Interp_IEU]>;
def : WriteRes<WriteCTZ32, [Interp_IEU]>;

let Latency = 2 in {
  def : WriteRes<WriteCPOP, [Interp_IEU]>;
  def : WriteRes<WriteCPOP32, [Interp_IEU]>;
}

def : WriteRes<WriteORCB, [Interp_IEU]>;
def : WriteRes<WriteIMinMax, [Interp_IEU]>;
def : WriteRes<WriteREV8, [Interp_IEU]>;

let Latency = 2 in {
  def : WriteRes<WriteSHXADD, [Interp_IEU]>;
  def : WriteRes<WriteSHXADD32, [Interp_IEU]>;
  def : WriteRes<WriteCLMUL, [Interp_IEU]>;
}

// Single-bit instructions
def : WriteRes<WriteSingleBit, [Interp_IEU]>;
def : WriteRes<WriteSingleBitImm, [Interp_IEU]>;
def : WriteRes<WriteBEXT, [Interp_IEU]>;
def : WriteRes<WriteBEXTI, [Interp_IEU]>;

// Memory/Atomic memory
let Latency = 4 in {
  def : WriteRes<WriteSTB, [Interp_LS]>;
  def : WriteRes<WriteSTH, [Interp_LS]>;
  def : WriteRes<WriteSTW, [Interp_LS]>;
  def : WriteRes<WriteSTD, [Interp_LS]>;
  def : WriteRes<WriteFST16, [Interp_LS]>;
  def : WriteRes<WriteFST32, [Interp_LS]>;
  def : WriteRes<WriteFST64, [Interp_LS]>;

  def : WriteRes<WriteLDB, [Interp_LS]>;
  def : WriteRes<WriteLDH, [Interp_LS]>;
  def : WriteRes<WriteLDW, [Interp_LS]>;
  def : WriteRes<WriteLDD, [Interp_LS]>;
  def : WriteRes<WriteFLD16, [Interp_LS]>;
  def : WriteRes<WriteFLD32, [Interp_LS]>;
  def : WriteRes<WriteFLD64, [Interp_LS]>;
}

// Atomics
let Latency = 8 in {
  def : WriteRes<WriteAtomicSTW, [Interp_LS]>;
  def : WriteRes<WriteAtomicSTD, [Interp_LS]>;
  def : WriteRes<WriteAtomicLDW, [Interp_LS]>;
  def : WriteRes<WriteAtomicLDD, [Interp_LS]>;
}

let Latency = 12 in {
  def : WriteRes<WriteAtomicW, [Interp_LS]>;
  def : WriteRes<WriteAtomicD, [Interp_LS]>;
}

// Floating point units Half precision
let Latency = 4 in {
  def : WriteRes<WriteFAdd16, [Interp_FP]>;
  def : WriteRes<WriteFMul16, [Interp_FP]>;
  def : WriteRes<WriteFSGNJ16, [Interp_FP]>;
  def : WriteRes<WriteFMinMax16, [Interp_FP]>;
}
def : WriteRes<WriteFMA16, [Interp_FP]> { let Latency = 5; }

let Latency = 12, ReleaseAtCycles = [12] in {
  def :  WriteRes<WriteFDiv16, [Interp_FP]>;
  def :  WriteRes<WriteFSqrt16, [Interp_FP]>;
}

// Single precision
let Latency = 4 in {
  def : WriteRes<WriteFAdd32, [Interp_FP]>;
  def : WriteRes<WriteFMul32, [Interp_FP]>;
  def : WriteRes<WriteFSGNJ32, [Interp_FP]>;
  def : WriteRes<WriteFMinMax32, [Interp_FP]>;
}
def : WriteRes<WriteFMA32, [Interp_FP]> { let Latency = 5; }

let Latency = 15, ReleaseAtCycles = [15] in {
  def :  WriteRes<WriteFDiv32, [Interp_FP]>;
  def :  WriteRes<WriteFSqrt32, [Interp_FP]>;
}

// Double precision
let Latency = 5 in {
  def : WriteRes<WriteFAdd64, [Interp_FP]>;
  def : WriteRes<WriteFMul64, [Interp_FP]>;
  def : WriteRes<WriteFSGNJ64, [Interp_FP]>;
}
def : WriteRes<WriteFMinMax64, [Interp_FP]> { let Latency = 4; }
def : WriteRes<WriteFMA64, [Interp_FP]> { let Latency = 6; }

let Latency = 22, ReleaseAtCycles = [22] in {
  def :  WriteRes<WriteFDiv64, [Interp_FP]>;
  def :  WriteRes<WriteFSqrt64, [Interp_FP]>;
}

// Conversions
let Latency = 6 in {
  def : WriteRes<WriteFCvtF16ToI32, [Interp_IEU]>;
  def : WriteRes<WriteFCvtF32ToI32, [Interp_IEU]>;
  def : WriteRes<WriteFCvtF32ToI64, [Interp_IEU]>;
  def : WriteRes<WriteFCvtF64ToI64, [Interp_IEU]>;
  def : WriteRes<WriteFCvtF64ToI32, [Interp_IEU]>;
  def : WriteRes<WriteFCvtF16ToI64, [Interp_IEU]>;
}

let Latency = 4 in {
  def : WriteRes<WriteFCvtI32ToF16, [Interp_IEU]>;
  def : WriteRes<WriteFCvtI32ToF32, [Interp_IEU]>;
  def : WriteRes<WriteFCvtI32ToF64, [Interp_IEU]>;
  def : WriteRes<WriteFCvtI64ToF16, [Interp_IEU]>;
  def : WriteRes<WriteFCvtI64ToF32, [Interp_IEU]>;
  def : WriteRes<WriteFCvtI64ToF64, [Interp_IEU]>;
  def : WriteRes<WriteFCvtF16ToF32, [Interp_FP]>;
  def : WriteRes<WriteFCvtF16ToF64, [Interp_FP]>;
  def : WriteRes<WriteFCvtF32ToF16, [Interp_FP]>;
  def : WriteRes<WriteFCvtF32ToF64, [Interp_FP]>;
  def : WriteRes<WriteFCvtF64ToF16, [Interp_FP]>;
  def : WriteRes<WriteFCvtF64ToF32, [Interp_FP]>;
}

let Latency = 6 in {
  def : WriteRes<WriteFClass16, [Interp_FP]>;
  def : WriteRes<WriteFClass32, [Interp_FP]>;
  def : WriteRes<WriteFClass64, [Interp_FP]>;

  def : WriteRes<WriteFCmp16, [Interp_FP]>;
  def : WriteRes<WriteFCmp32, [Interp_FP]>;
  def : WriteRes<WriteFCmp64, [Interp_FP]>;

  def : WriteRes<WriteFMovF32ToI32, [Interp_IEU]>;
  def : WriteRes<WriteFMovF16ToI16, [Interp_IEU]>;
}

let Latency = 4 in {
  def : WriteRes<WriteFMovI16ToF16, [Interp_IEU]>;
  def : WriteRes<WriteFMovF64ToI64, [Interp_IEU]>;
  def : WriteRes<WriteFMovI64ToF64, [Interp_IEU]>;
  def : WriteRes<WriteFMovI32ToF32, [Interp_IEU]>;
}

// 6. Configuration-Setting Instructions
def : WriteRes<WriteVSETVLI, [Interp_IEUA]>;
def : WriteRes<WriteVSETIVLI, [Interp_IEUA]>;
def : WriteRes<WriteVSETVL, [Interp_IEUA]>;

// 7. Vector Loads and Stores
foreach mx = SchedMxList in {
  defvar IsWorstCase = InterpIsWorstCaseMX<mx, SchedMxList>.c;

  // Unit-stride loads and stores
  defvar VLDELatAndOcc = InterpConstValueUntilLMULThenDoubleBase<"M2", 3, 4, mx>.c;
  let Latency = VLDELatAndOcc, ReleaseAtCycles = [VLDELatAndOcc] in {
    defm "" : LMULWriteResMX<"WriteVLDE", [Interp_VLS], mx, IsWorstCase>;
  }
  defvar VSTELatAndOcc = InterpGetLMULValue<[2, 2, 2, 3, 4, 8, 19], mx>.c;
  let Latency = VSTELatAndOcc, ReleaseAtCycles = [VSTELatAndOcc] in {
    defm "" : LMULWriteResMX<"WriteVSTE", [Interp_VLS], mx, IsWorstCase>;
  }
  defvar VLDFFLatAndOcc = InterpGetLMULValue<[4, 4, 4, 5, 7, 11, 19], mx>.c;
  let Latency = VLDFFLatAndOcc, ReleaseAtCycles = [VLDFFLatAndOcc] in {
    defm "" : LMULWriteResMX<"WriteVLDFF", [Interp_VLS], mx, IsWorstCase>;
  }

  // Mask loads and stores
  let ReleaseAtCycles = [2] in {
    defm "" : LMULWriteResMX<"WriteVLDM", [Interp_VLS], mx, IsWorstCase>;
  }
  let Latency = 2, ReleaseAtCycles = [2] in {
    defm "" : LMULWriteResMX<"WriteVSTM", [Interp_VLS], mx, IsWorstCase>;
  }

  // Strided and indexed loads and stores
  foreach eew = [8, 16, 32, 64] in {
    defvar StridedLdStLatAndOcc = InterpGetVLMAX<mx, eew>.val;
    let Latency = StridedLdStLatAndOcc, ReleaseAtCycles = [StridedLdStLatAndOcc] in {
      defm "" : LMULWriteResMX<"WriteVLDS"  # eew, [Interp_VLS], mx, IsWorstCase>;
      defm "" : LMULWriteResMX<"WriteVSTS"  # eew, [Interp_VLS], mx, IsWorstCase>;
    }

    defvar IndexedLdStLatAndOcc = !div(InterpGetVLMAX<mx, eew>.val, 2);
    let Latency = IndexedLdStLatAndOcc, ReleaseAtCycles = [IndexedLdStLatAndOcc] in {
      defm "" : LMULWriteResMX<"WriteVLDUX" # eew, [Interp_VLS], mx, IsWorstCase>;
      defm "" : LMULWriteResMX<"WriteVLDOX" # eew, [Interp_VLS], mx, IsWorstCase>;

      defm "" : LMULWriteResMX<"WriteVSTUX" # eew, [Interp_VLS], mx, IsWorstCase>;
      defm "" : LMULWriteResMX<"WriteVSTOX" # eew, [Interp_VLS], mx, IsWorstCase>;
    }
  }
}

// Segmented loads and stores
foreach mx = SchedMxList in {
  foreach nf=2-8 in {
    foreach eew = [8, 16, 32, 64] in {
      defvar IsWorstCase = InterpIsWorstCaseMX<mx, SchedMxList>.c;

      defvar SegmentedLdStLatAndOcc = InterpSegmentedLdStCycles<mx, eew, nf>.c;
      let Latency = SegmentedLdStLatAndOcc, ReleaseAtCycles = [SegmentedLdStLatAndOcc] in {
        // Unit-stride segmented
        defm "" : LMULWriteResMX<"WriteVLSEG" # nf # "e" #eew, [Interp_VLS], mx, IsWorstCase>;
        defm "" : LMULWriteResMX<"WriteVLSEGFF" # nf # "e" #eew, [Interp_VLS], mx, IsWorstCase>;
        defm "" : LMULWriteResMX<"WriteVSSEG" # nf # "e" #eew, [Interp_VLS], mx, IsWorstCase>;

        // Strided/indexed segmented
        defm "" : LMULWriteResMX<"WriteVLSSEG" # nf # "e" #eew, [Interp_VLS], mx, IsWorstCase>;
        defm "" : LMULWriteResMX<"WriteVSSSEG" # nf # "e" #eew, [Interp_VLS], mx, IsWorstCase>;

        // Indexed segmented
        defm "" : LMULWriteResMX<"WriteVLOXSEG" # nf # "e" #eew, [Interp_VLS], mx, IsWorstCase>;
        defm "" : LMULWriteResMX<"WriteVLUXSEG" # nf # "e" #eew, [Interp_VLS], mx, IsWorstCase>;
        defm "" : LMULWriteResMX<"WriteVSUXSEG" # nf # "e" #eew, [Interp_VLS], mx, IsWorstCase>;
        defm "" : LMULWriteResMX<"WriteVSOXSEG" # nf # "e" #eew, [Interp_VLS], mx, IsWorstCase>;
      }
    }
  }
}

// Whole register move/load/store
foreach LMul = [1, 2, 4, 8] in {
  defvar WholeRegLdStLatAndOcc = !if(!eq(LMul, 1), 3, !mul(LMul, 2));
  let Latency = WholeRegLdStLatAndOcc, ReleaseAtCycles = [WholeRegLdStLatAndOcc] in {
    def : WriteRes<!cast<SchedWrite>("WriteVLD" # LMul # "R"), [Interp_VLS]>;
    def : WriteRes<!cast<SchedWrite>("WriteVST" # LMul # "R"), [Interp_VLS]>;
  }

  defvar VMovLatAndOcc = !if(!eq(LMul, 1), 4, !mul(LMul, 2));
  let Latency = VMovLatAndOcc, ReleaseAtCycles = [VMovLatAndOcc] in {
    def : WriteRes<!cast<SchedWrite>("WriteVMov" # LMul # "V"), [Interp_VIEU]>;
  }
}

// 11. Vector Integer Arithmetic Instructions
foreach mx = SchedMxList in {
  defvar IsWorstCase = InterpIsWorstCaseMX<mx, SchedMxList>.c;

  let Latency = InterpGet4458Latency<mx>.c, ReleaseAtCycles = [InterpConstOneUntilM1ThenDouble<mx>.c] in {
    defm "" : LMULWriteResMX<"WriteVIMinMaxV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIMinMaxX", [Interp_VIEU], mx, IsWorstCase>;
  }

  // Latency of vadd, vsub, vrsub:         4/4/5/8
  // ReleaseAtCycles of vadd, vsub, vrsub: 1/2/4/8
  // Latency of vand, vor, vxor:           4/4/8/16
  // ReleaseAtCycles of vand, vor, vxor:   2/4/8/16
  // They are grouped together, so we used the worst case 4/4/8/16 and 2/4/8/16
  // TODO: use InstRW to override individual instructions' scheduling data
  defvar VIALULat = InterpConstValueUntilLMULThenDouble<"M2", 4, mx>.c;
  defvar VIALUOcc = InterpConstOneUntilMF2ThenDouble<mx>.c;
  let Latency = VIALULat, ReleaseAtCycles = [VIALUOcc] in {
    defm "" : LMULWriteResMX<"WriteVIALUV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIALUX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIALUI", [Interp_VIEU], mx, IsWorstCase>;
  }

  let Latency = VIALULat in
  def InterpWriteVCOPY_ # mx : SchedWriteRes<[]>;

  defvar VILogicalLat = InterpConstValueUntilLMULThenDouble<"M2", 4, mx>.c;
  defvar VILogicalOcc = InterpConstValueUntilLMULThenDouble<"MF2", 1, mx>.c;
  let Latency = VILogicalLat, ReleaseAtCycles = [VILogicalOcc] in {
    defm "" : LMULWriteResMX<"WriteVExtV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIMergeV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIMergeX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIMergeI", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIMovV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIMovX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIMovI", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVShiftV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVShiftX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVShiftI", [Interp_VIEU], mx, IsWorstCase>;

    defm "" : LMULWriteResMX<"WriteVICALUV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVICALUX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVICALUI", [Interp_VIEU], mx, IsWorstCase>;
  }

  // Slightly increase Occ when LMUL == M8
  defvar VICmpCarryOcc = InterpGetLMULValue<[1, 1, 1, 2, 4, 8, 18], mx>.c;
  let Latency = InterpGet461018Latency<mx>.c, ReleaseAtCycles = [VICmpCarryOcc] in {
    defm "" : LMULWriteResMX<"WriteVICALUMV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVICALUMX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVICALUMI", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVICmpV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVICmpX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVICmpI", [Interp_VIEU], mx, IsWorstCase>;
  }

  // Latency of vmacc, vmadd, vmul, vmulh, etc.: e8/e16 = 4/4/5/8, e32 = 5,5,5,8,
  // e64 = 7,8,16,32. We use the worst-case until we can split the SEW.
  // TODO: change WriteVIMulV, etc to be defined with LMULSEWSchedWrites
  defvar VIMulLat = InterpConstValueUntilLMULThenDoubleBase<"M2", 7, 8, mx>.c;
  // ReleaseAtCycles for vnmsac/vnmsub is 1/1/1/1/2/5 but we use the worse case
  // here since they are grouped together with vmacc/vmadd/vmul/vmulh.
  defvar VIMulOcc = InterpConstOneUntilM1ThenDouble<mx>.c;
  let Latency = VIMulLat, ReleaseAtCycles = [VIMulOcc] in {
    defm "" : LMULWriteResMX<"WriteVIMulV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIMulX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIMulAddV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIMulAddX", [Interp_VIEU], mx, IsWorstCase>;
  }
}

// Widening
// Pattern of vwmul, vwmacc, etc: e8/e16 = 4/4/5/8, e32 = 5,5,5,8
// We use the worst-case for all.
foreach mx = SchedMxListW in {
  defvar IsWorstCase = InterpIsWorstCaseMX<mx, SchedMxListW>.c;

  defvar VIWideningOcc = InterpConstOneUntilMF2ThenDouble<mx>.c;
  let Latency = InterpGet4588Latency<mx>.c, ReleaseAtCycles = [VIWideningOcc]  in {
    defm "" : LMULWriteResMX<"WriteVIWALUV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIWALUX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIWALUI", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIWMulV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIWMulX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIWMulAddV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIWMulAddX", [Interp_VIEU], mx, IsWorstCase>;
  }
}

// Division and remainder operations
// Pattern of vdivu: 11/11/11/20/40/80/160
// Pattern of vdiv: 12/12/12/22/44/88/176
// Pattern of vremu: 12/12/12/22/44/88/176
// Pattern of vrem: 13/13/13/24/48/96/192
// We use for all: 12/12/12/24/48/96/192
// TODO: Create separate WriteVIRem to more closely match the latencies
foreach mx = SchedMxList in {
  foreach sew = SchedSEWSet<mx>.val in {
    defvar IsWorstCase = InterpIsWorstCaseMXSEW<mx, sew, SchedMxList>.c;

    // Not pipelined
    defvar VIDivLatAndOcc = InterpConstValueUntilLMULThenDouble<"MF2", 12, mx>.c;
    let Latency = VIDivLatAndOcc, ReleaseAtCycles = [VIDivLatAndOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVIDivV", [Interp_VIEU], mx, sew, IsWorstCase>;
      defm "" : LMULSEWWriteResMXSEW<"WriteVIDivX", [Interp_VIEU], mx, sew, IsWorstCase>;
    }
  }
}

// Narrowing Shift and Clips
foreach mx = SchedMxListW in {
  defvar IsWorstCase = InterpIsWorstCaseMX<mx, SchedMxListW>.c;

  defvar VNarrowingLat = InterpConstValueUntilLMULThenDouble<"M1", 4, mx>.c;
  defvar VNarrowingOcc = InterpConstValueUntilLMULThenDouble<"MF4", 1, mx>.c;
  let Latency = VNarrowingLat, ReleaseAtCycles = [VNarrowingOcc] in {
    defm "" : LMULWriteResMX<"WriteVNShiftV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVNShiftX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVNShiftI", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVNClipV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVNClipX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVNClipI", [Interp_VIEU], mx, IsWorstCase>;
  }
}

// 12. Vector Fixed-Point Arithmetic Instructions
foreach mx = SchedMxList in {
  defvar IsWorstCase = InterpIsWorstCaseMX<mx, SchedMxList>.c;

  let Latency = InterpGet4458Latency<mx>.c, ReleaseAtCycles = [InterpConstOneUntilM1ThenDouble<mx>.c] in {
    defm "" : LMULWriteResMX<"WriteVSALUV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVSALUX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVSALUI", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVAALUV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVAALUX", [Interp_VIEU], mx, IsWorstCase>;
  }

  // Latency of vsmul: e8/e16 = 4/4/5/8, e32 = 5/5/5/8, e64 = 7/8/16/32
  // We use the worst-case until we can split the SEW.
  defvar VSMulLat = InterpConstValueUntilLMULThenDoubleBase<"M2", 7, 8, mx>.c;
  // Latency of vsmul: e8/e16/e32 = 1/2/4/8, e64 = 4/8/16/32
  // We use the worst-case until we can split the SEW.
  defvar VSMulOcc = InterpConstValueUntilLMULThenDoubleBase<"M1", 1, 4, mx>.c;
  // TODO: change WriteVSMulV/X to be defined with LMULSEWSchedWrites
  let Latency = VSMulLat, ReleaseAtCycles = [VSMulOcc] in {
    defm "" : LMULWriteResMX<"WriteVSMulV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVSMulX", [Interp_VIEU], mx, IsWorstCase>;
  }

  defvar VSShiftLat = InterpConstValueUntilLMULThenDouble<"M2", 4, mx>.c;
  defvar VSShiftOcc = InterpConstOneUntilMF2ThenDouble<mx>.c;
  let Latency = VSShiftLat, ReleaseAtCycles = [VSShiftOcc] in {
    defm "" : LMULWriteResMX<"WriteVSShiftV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVSShiftX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVSShiftI", [Interp_VIEU], mx, IsWorstCase>;
  }
}

// 13. Vector Floating-Point Instructions
foreach mx = SchedMxListF in {
  foreach sew = SchedSEWSet<mx, isF=1>.val in {
    defvar IsWorstCase = InterpIsWorstCaseMXSEW<mx, sew, SchedMxListF, isF=1>.c;

    defvar VFALULat = InterpGet4458Latency<mx>.c;
    defvar VFALUOcc = InterpConstOneUntilM1ThenDouble<mx>.c;
    let Latency = VFALULat, ReleaseAtCycles = [VFALUOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFALUV", [Interp_VFP], mx, sew, IsWorstCase>;
      defm "" : LMULSEWWriteResMXSEW<"WriteVFALUF", [Interp_VFP], mx, sew, IsWorstCase>;
      defm "" : LMULSEWWriteResMXSEW<"WriteVFMinMaxV", [Interp_VFP], mx, sew, IsWorstCase>;
      defm "" : LMULSEWWriteResMXSEW<"WriteVFMinMaxF", [Interp_VFP], mx, sew, IsWorstCase>;
    }

    // Slightly increased latency for sew == 64
    defvar VFMulVLat = !if(!eq(sew, 64), InterpConstValueUntilLMULThenDoubleBase<"M8", 5, 8, mx>.c,
                                               InterpGet4458Latency<mx>.c);
    let Latency = VFMulVLat, ReleaseAtCycles = [InterpConstOneUntilM1ThenDouble<mx>.c] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFMulV", [Interp_VFP], mx, sew, IsWorstCase>;
    }
    // VFMulF has the same latency as VFMulV, but slighlty lower ReleaseAtCycles
    let Latency = VFMulVLat, ReleaseAtCycles = [InterpConstOneUntilM1ThenDouble<mx>.c] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFMulF", [Interp_VFP], mx, sew, IsWorstCase>;
    }

    defvar VFSgnjLat = InterpConstValueUntilLMULThenDouble<"M2", 4, mx>.c;
    defvar VFSgnjOcc = InterpConstOneUntilMF2ThenDouble<mx>.c;
    let Latency = VFSgnjLat, ReleaseAtCycles = [VFSgnjOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFRecpV", [Interp_VFP], mx, sew, IsWorstCase>;
      defm "" : LMULSEWWriteResMXSEW<"WriteVFSgnjV", [Interp_VFP], mx, sew, IsWorstCase>;
      defm "" : LMULSEWWriteResMXSEW<"WriteVFSgnjF", [Interp_VFP], mx, sew, IsWorstCase>;
      defm "" : LMULSEWWriteResMXSEW<"WriteVFCvtIToFV", [Interp_VFP], mx, sew, IsWorstCase>;
    }

    // The following covers vfmacc, vfmsac, and their vfn* variants in the same group, but the
    // ReleaseAtCycles takes one extra cycle for the vfn* variants.
    // TODO: Should we split them?
    // TODO: for some reason, the following cond is not working, and always use InterpConstValueUntilLMULThenDoubleBase<"M4", 5, 8, mx>.c
    defvar VFMulAddLatency = !if(!eq(sew, 64),
      InterpGet6678Latency<mx>.c,
      InterpConstValueUntilLMULThenDoubleBase<"M8", 5, 8, mx>.c
    );
    let Latency = VFMulAddLatency, ReleaseAtCycles = [InterpConstOneUntilM1ThenDouble<mx>.c] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFMulAddV", [Interp_VFP], mx, sew, IsWorstCase>;
      defm "" : LMULSEWWriteResMXSEW<"WriteVFMulAddF", [Interp_VFP], mx, sew, IsWorstCase>;
    }
  }
}

foreach mx = SchedMxList in {
  defvar IsWorstCase = InterpIsWorstCaseMX<mx, SchedMxList>.c;

  // Slightly increased ReleaseAtCycles for M8: 18
  defvar VFCmpOcc = !if(!eq(mx, "M8"),
    !add(InterpConstOneUntilMF2ThenDouble<mx>.c, 2),
    InterpConstOneUntilMF2ThenDouble<mx>.c
  );
  let Latency = InterpGet461018Latency<mx>.c, ReleaseAtCycles = [VFCmpOcc] in {
    defm "" : LMULWriteResMX<"WriteVFCmpV", [Interp_VFP], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVFCmpF", [Interp_VFP], mx, IsWorstCase>;
  }

  defvar VFClassLat = InterpConstValueUntilLMULThenDouble<"M2", 4, mx>.c;
  defvar VFClassOcc = InterpConstOneUntilMF2ThenDouble<mx>.c;
  let Latency = VFClassLat, ReleaseAtCycles = [VFClassOcc] in {
    defm "" : LMULWriteResMX<"WriteVFClassV", [Interp_VFP], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVFMergeV", [Interp_VFP], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVFMovV", [Interp_VFP], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVFCvtFToIV", [Interp_VFP], mx, IsWorstCase>;
  }
}

// Widening
foreach mx = SchedMxListW in {
  foreach sew = SchedSEWSet<mx, isF=0, isWidening=1>.val in {
    defvar IsWorstCase = InterpIsWorstCaseMXSEW<mx, sew, SchedMxListW>.c;

    defvar VFWCvtILat = InterpConstValueUntilLMULThenDouble<"M1", 4, mx>.c;
    defvar VFWCvtIOcc = InterpConstOneUntilMF4ThenDouble<mx>.c;
    let Latency = VFWCvtILat, ReleaseAtCycles = [VFWCvtIOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFWCvtIToFV", [Interp_VFP], mx, sew, IsWorstCase>;
    }
  }
}

foreach mx = SchedMxListFW in {
  defvar IsWorstCase = InterpIsWorstCaseMX<mx, SchedMxListFW>.c;

  defvar VFWCvtFToIVLat = InterpConstValueUntilLMULThenDouble<"M1", 4, mx>.c;
  defvar VFWCvtFToIVOcc = InterpConstOneUntilMF4ThenDouble<mx>.c;
  let Latency = VFWCvtFToIVLat, ReleaseAtCycles = [VFWCvtFToIVOcc] in {
    defm "" : LMULWriteResMX<"WriteVFWCvtFToIV", [Interp_VFP], mx, IsWorstCase>;
  }
}

foreach mx = SchedMxListFW in {
  foreach sew = SchedSEWSet<mx, isF=1, isWidening=1>.val in {
    defvar IsWorstCase = InterpIsWorstCaseMXSEW<mx, sew, SchedMxListFW, isF=1>.c;

    defvar VFWCvtFToFVLat = InterpConstValueUntilLMULThenDouble<"M1", 4, mx>.c;
    defvar VFWCvtFToFVOcc = InterpConstOneUntilMF4ThenDouble<mx>.c;
    let Latency = VFWCvtFToFVLat, ReleaseAtCycles = [VFWCvtFToFVOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFWCvtFToFV", [Interp_VFP], mx, sew, IsWorstCase>;
    }

    // Latency for vfwsub/vfwadd.vv, vfwsub/vfwadd.vf: 4/4/4/5/8
    // ReleaseAtCycles for vfwsub/vfwadd.vv, vfwsub/vfwadd.vf: 1/1/2/4/8
    // Latency for vfwsub/vfwadd.wv, vfwsub/vfwadd.wf: 5/5/5/9/17
    // ReleaseAtCycles for vfwsub/vfwadd.wv, vfwsub/vfwadd.wf: 1/2/4/8/17
    // We use the worst-case
    defvar VFWALULat = !add(InterpConstValueUntilLMULThenDouble<"M1", 4, mx>.c, 1); // 5/5/9/17
    defvar VFWALUOcc = !if(!eq(mx, "M4"),
      !add(InterpConstOneUntilMF4ThenDouble<mx>.c, 1), // 2/4/8/17
      InterpConstOneUntilMF4ThenDouble<mx>.c
    );
    // TODO: Split .wf/.wv variants into separate scheduling classes
    let Latency = VFWALULat, ReleaseAtCycles = [VFWALUOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFWALUV", [Interp_VFP], mx, sew, IsWorstCase>;
      defm "" : LMULSEWWriteResMXSEW<"WriteVFWALUF", [Interp_VFP], mx, sew, IsWorstCase>;
    }

    let Latency = InterpGet4588Latency<mx>.c, ReleaseAtCycles = [InterpConstOneUntilMF2ThenDouble<mx>.c] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFWMulF", [Interp_VFP], mx, sew, IsWorstCase>;
    }

    // Slightly increased latency for SEW == 32
    defvar VFWMullOcc = !if(!eq(sew, 32),
      InterpGetLMULValue<[1, 1, 1, 3, 5, 9, 18], mx>.c,
      InterpConstOneUntilMF2ThenDouble<mx>.c
    );
    defvar VFWMulVLat = InterpConstValueUntilLMULThenDoubleBase<"M8", 5, 8, mx>.c;
    let Latency = VFWMulVLat, ReleaseAtCycles = [VFWMullOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFWMulV", [Interp_VFP], mx, sew, IsWorstCase>;
    }

    // Latency for vfwmacc, vfwnmacc, etc: e16 = 5/5/5/8; e32 = 6/6/7/8
    defvar VFWMulAddVLat = !if(!eq(sew, 16),
      InterpConstValueUntilLMULThenDoubleBase<"M4", 5, 8, mx>.c,
      InterpGet6678Latency<mx>.c
    );
    let Latency = VFWMulAddVLat, ReleaseAtCycles = [InterpConstOneUntilMF2ThenDouble<mx>.c] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFWMulAddV", [Interp_VFP], mx, sew, IsWorstCase>;
      defm "" : LMULSEWWriteResMXSEW<"WriteVFWMulAddF", [Interp_VFP], mx, sew, IsWorstCase>;
    }
  }
}

// Narrowing
foreach mx = SchedMxListW in {
  defvar IsWorstCase = InterpIsWorstCaseMX<mx, SchedMxListW>.c;

  defvar VFNCvtFToIVLat = InterpConstValueUntilLMULThenDouble<"M1", 4, mx>.c;
  defvar VFNCvtFToIVOcc = InterpConstOneUntilMF4ThenDouble<mx>.c;
  let Latency = VFNCvtFToIVLat, ReleaseAtCycles = [VFNCvtFToIVOcc] in {
    defm "" : LMULWriteResMX<"WriteVFNCvtFToIV", [Interp_VFP], mx, IsWorstCase>;
  }
}

foreach mx = SchedMxListFW in {
  foreach sew = SchedSEWSet<mx, isF=1, isWidening=1>.val in {
    defvar IsWorstCase = InterpIsWorstCaseMXSEW<mx, sew, SchedMxListFW, isF=1>.c;

    defvar VFNCvtToFVLat = InterpConstValueUntilLMULThenDouble<"M1", 4, mx>.c;
    defvar VFNCvtToFVOcc = InterpConstOneUntilMF4ThenDouble<mx>.c;
    let Latency = VFNCvtToFVLat, ReleaseAtCycles = [VFNCvtToFVOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFNCvtIToFV", [Interp_VFP], mx, sew, IsWorstCase>;
      defm "" : LMULSEWWriteResMXSEW<"WriteVFNCvtFToFV", [Interp_VFP], mx, sew, IsWorstCase>;
    }
  }
}

// Vector Floating-Point Division and Square Root
foreach mx = SchedMxListF in {
  foreach sew = SchedSEWSet<mx, 1>.val in {
    defvar IsWorstCase = InterpIsWorstCaseMXSEW<mx, sew, SchedMxListF, 1>.c;

    // Compute ReleaseAtCycles based on SEW
    // Latency for vfdiv.vf: e16/e32 = 12/24/48/96; e64 = 18/36/72/144
    // Latency for vfrdiv.vf: e16/e32 = 12/24/48/96; e64 = 40/80/160/320
    // We use the worst-case, vfdiv.vf is penalized in e64
    // TODO: split vfdiv.vf and vfrdiv.vf into separate scheduling classes
    defvar VFDivFFactor = !if(!eq(sew, 64), 40, 12);
    defvar VFDivFLatAndOcc = !mul(InterpConstOneUntilM1ThenDouble<mx>.c, VFDivFFactor);
    let Latency = VFDivFLatAndOcc, ReleaseAtCycles = [VFDivFLatAndOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFDivF", [Interp_VFP], mx, sew, IsWorstCase>;
    }

    defvar VFDivVFactor = !if(!eq(sew, 16), 12, 40);
    defvar VFDivVLatAndOcc = !mul(InterpConstOneUntilM1ThenDouble<mx>.c, VFDivVFactor);
    let Latency = VFDivVLatAndOcc, ReleaseAtCycles = [VFDivVLatAndOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFDivV", [Interp_VFP], mx, sew, IsWorstCase>;
    }
  }
}

// Pattern for vfsqrt.v: e16 = 18/36/72/144; e32 = 38/76/152/304; e64 = 40/80/160/320
foreach mx = SchedMxListF in {
  foreach sew = SchedSEWSet<mx, 1>.val in {
    defvar IsWorstCase = InterpIsWorstCaseMXSEW<mx, sew, SchedMxListF, 1>.c;

    defvar VFSqrtVFactor = !if(!eq(sew, 16), 12, 40);
    defvar VFSqrtVLatAndOcc = !mul(InterpConstOneUntilM1ThenDouble<mx>.c, VFSqrtVFactor);
    let Latency = VFSqrtVLatAndOcc, ReleaseAtCycles = [VFSqrtVLatAndOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFSqrtV", [Interp_VFP], mx, sew, IsWorstCase>;
    }
  }
}

// 14. Vector Reduction Operations
foreach mx = SchedMxList in {
  foreach sew = SchedSEWSet<mx>.val in {
    defvar IsWorstCase = InterpIsWorstCaseMXSEW<mx, sew, SchedMxList>.c;

    defvar VIRedLat = InterpGetLMULValue<[5, 5, 5, 7, 11, 19, 35], mx>.c;
    defvar VIRedOcc = InterpGetLMULValue<[1, 1, 2, 2, 4, 10, 35], mx>.c;
    let Latency = VIRedLat, ReleaseAtCycles = [VIRedOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVIRedMinMaxV_From", [Interp_VIEU], mx, sew, IsWorstCase>;

      // Pattern for vredsum:                  5/5/5/7/11/19/35
      // Pattern for vredand, vredor, vredxor: 4/4/4/6/10/18/34
      // They are grouped together, so we use the worst-case vredsum latency.
      // TODO: split vredand, vredor, vredxor into separate scheduling classe.
      defm "" : LMULSEWWriteResMXSEW<"WriteVIRedV_From", [Interp_VIEU], mx, sew, IsWorstCase>;
    }
  }
}

foreach mx = SchedMxListWRed in {
  foreach sew = SchedSEWSet<mx, 0, 1>.val in {
    defvar IsWorstCase = InterpIsWorstCaseMXSEW<mx, sew, SchedMxListWRed>.c;

    defvar VIRedLat = InterpGetLMULValue<[5, 5, 5, 7, 11, 19, 35], mx>.c;
    defvar VIRedOcc = InterpGetLMULValue<[1, 1, 2, 2, 4, 10, 35], mx>.c;
    let Latency = VIRedLat, ReleaseAtCycles = [VIRedOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVIWRedV_From", [Interp_VIEU], mx, sew, IsWorstCase>;
    }
  }
}

foreach mx = SchedMxListF in {
  foreach sew = SchedSEWSet<mx, 1>.val in {
    defvar IsWorstCase = InterpIsWorstCaseMXSEW<mx, sew, SchedMxListF, 1>.c;

    // Latency for vfredmax.vs, vfredmin.vs: 12/12/15/21/33/57
    // Latency for vfredusum.vs is slightly lower for e16/e32
    // We use the worst-case
    defvar VFRedLat = InterpGetLMULValue<[12, 12, 12, 15, 21, 33, 57], mx>.c;
    defvar VFRedOcc = InterpGetLMULValue<[8, 8, 8, 8, 14, 20, 57], mx>.c;
    let Latency = VFRedLat, ReleaseAtCycles = [VFRedOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFRedV_From", [Interp_VFP], mx, sew, IsWorstCase>;
      defm "" : LMULSEWWriteResMXSEW<"WriteVFRedMinMaxV_From", [Interp_VFP], mx, sew, IsWorstCase>;
    }
  }
}

foreach mx = SchedMxListF in {
  foreach sew = SchedSEWSet<mx, 1>.val in {
    defvar IsWorstCase = InterpIsWorstCaseMXSEW<mx, sew, SchedMxListF, 1>.c;

    // Compute latency based on SEW
    defvar VFRedOV_FromLat = !cond(
      !eq(sew, 16) : InterpConstValueUntilLMULThenDouble<"MF4", 12, mx>.c,
      !eq(sew, 32) : InterpConstValueUntilLMULThenDouble<"MF2", 12, mx>.c,
      !eq(sew, 64) : InterpConstValueUntilLMULThenDouble<"M1", 12, mx>.c
    );
    defvar VFRedOV_FromOcc = !cond(
      !eq(sew, 16) : InterpGetLMULValue<[8, 8, 20, 24, 48, 96, 384], mx>.c,
      !eq(sew, 32) : InterpGetLMULValue<[8, 8,  8, 12, 24, 48, 192], mx>.c,
      !eq(sew, 64) : InterpGetLMULValue<[6, 6,  6,  6, 12, 24,  96], mx>.c
    );
    let Latency = VFRedOV_FromLat, ReleaseAtCycles = [VFRedOV_FromOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFRedOV_From", [Interp_VFP], mx, sew, IsWorstCase>;
    }
  }
}

foreach mx = SchedMxListFWRed in {
  foreach sew = SchedSEWSet<mx, 1, 1>.val in {
    defvar IsWorstCase = InterpIsWorstCaseMXSEW<mx, sew, SchedMxListFWRed, 1>.c;

    defvar VFRedOVLat = !cond(
      !eq(sew, 16) : InterpConstValueUntilLMULThenDouble<"MF4", 16, mx>.c,
      !eq(sew, 32) : InterpConstValueUntilLMULThenDouble<"MF2", 16, mx>.c,
    );
    defvar VFRedOVOcc = !cond(
      !eq(sew, 16) : InterpGetLMULValue<[11, 11, 27, 32, 64, 128, 512], mx>.c,
      !eq(sew, 32) : InterpGetLMULValue<[11, 11, 11, 16, 32,  64, 256], mx>.c,
    );
    let Latency = VFRedOVLat, ReleaseAtCycles = [VFRedOVOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVFWRedV_From", [Interp_VFP], mx, sew, IsWorstCase>;
      defm "" : LMULSEWWriteResMXSEW<"WriteVFWRedOV_From", [Interp_VFP], mx, sew, IsWorstCase>;
    }
  }
}

// 15. Vector Mask Instructions
foreach mx = SchedMxList in {
  defvar IsWorstCase = InterpIsWorstCaseMX<mx, SchedMxList>.c;

  let Latency = 4 in {
    defm "" : LMULWriteResMX<"WriteVMALUV", [Interp_VIEU], mx, IsWorstCase>;
  }
  let Latency = 4, ReleaseAtCycles = [InterpConstValueUntilLMULThenDouble<"M2", 1, mx>.c] in {
    defm "" : LMULWriteResMX<"WriteVMSFSV", [Interp_VIEU], mx, IsWorstCase>;
  }

  let Latency = 6, ReleaseAtCycles = [2] in {
    defm "" : LMULWriteResMX<"WriteVMPopV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVMFFSV", [Interp_VIEU], mx, IsWorstCase>;
  }

  defvar VIotaLat = InterpConstValueUntilLMULThenDouble<"M2", 4, mx>.c;
  defvar VIotaOcc = InterpConstOneUntilMF2ThenDouble<mx>.c;
  let Latency = VIotaLat, ReleaseAtCycles = [VIotaOcc] in {
    defm "" : LMULWriteResMX<"WriteVIotaV", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVIdxV", [Interp_VIEU], mx, IsWorstCase>;
  }
}

// 16. Vector Permutation Instructions
// Slide
foreach mx = SchedMxList in {
  defvar IsWorstCase = InterpIsWorstCaseMX<mx, SchedMxList>.c;

  // Latency for slide up: 4/4/8/16, ReleaseAtCycles is 2/4/8/16
  defvar VSlideUpLat = InterpConstValueUntilLMULThenDouble<"M2", 4, mx>.c;
  defvar VSlideUpOcc = InterpConstOneUntilMF2ThenDouble<mx>.c;
  let Latency = VSlideUpLat, ReleaseAtCycles =[VSlideUpOcc] in {
    defm "" : LMULWriteResMX<"WriteVSlideUpX", [Interp_VIEU], mx, IsWorstCase>;
  }

  // Latency for slide down: 4/5/9/17, ReleaseAtCycles is 3/5/9/17
  defvar VSlideDownLat = InterpGetLMULValue<[4, 4, 4, 4, 5, 9, 17], mx>.c;
  defvar VSlideDownOcc = InterpGetLMULValue<[1, 1, 1, 3, 5, 9, 17], mx>.c;
  let Latency = VSlideDownLat, ReleaseAtCycles =[VSlideDownOcc] in {
    defm "" : LMULWriteResMX<"WriteVSlideDownX", [Interp_VIEU], mx, IsWorstCase>;
  }
  // The following group slide up and down together, so we use the worst-case
  // (slide down) for all.
  let Latency = VSlideDownLat, ReleaseAtCycles =[VSlideDownOcc] in {
    defm "" : LMULWriteResMX<"WriteVSlideUpI", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVSlideDownI", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVISlide1Up", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVISlide1Down", [Interp_VIEU], mx, IsWorstCase>;

    defm "" : LMULWriteResMX<"WriteVFSlide1Up", [Interp_VFP], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVFSlide1Down", [Interp_VFP], mx, IsWorstCase>;
  }
}

// ReleaseAtCycles is 2/2/2/2/2/3/6, but we can't set based on MX for now
// TODO: Split this into separate WriteRes for each MX
let Latency = 6, ReleaseAtCycles = [6] in {
  def : WriteRes<WriteVMovXS, [Interp_VIEU]>;
}

// ReleaseAtCycles is 1/1/1/1/1/2/4, but we can't set based on MX for now
// TODO: Split this into separate WriteRes for each MX
let Latency = 4, ReleaseAtCycles = [4] in {
  def : WriteRes<WriteVMovSX, [Interp_VIEU]>;
  def : WriteRes<WriteVMovFS, [Interp_VIEU]>;
  def : WriteRes<WriteVMovSF, [Interp_VIEU]>;
}

// Integer LMUL Gather and Compress
foreach mx = SchedMxList in {
  defvar IsWorstCase = InterpIsWorstCaseMX<mx, SchedMxList>.c;

  defvar VRGatherLat = InterpConstValueUntilLMULThenDouble<"M2", 4, mx>.c;
  let Latency = VRGatherLat, ReleaseAtCycles = [InterpConstOneUntilMF2ThenDouble<mx>.c] in {
    defm "" : LMULWriteResMX<"WriteVRGatherVX", [Interp_VIEU], mx, IsWorstCase>;
    defm "" : LMULWriteResMX<"WriteVRGatherVI", [Interp_VIEU], mx, IsWorstCase>;
  }

  foreach sew = SchedSEWSet<mx>.val in {
    defvar IsWorstCaseSEW = InterpIsWorstCaseMXSEW<mx, sew, SchedMxList>.c;

    defvar VRGatherVVLat = InterpGetLMULValue<[4, 4, 4, 4, 16, 64, 256], mx>.c;
    defvar VRGatherVVOcc = InterpGetLMULValue<[1, 1, 1, 4, 16, 64, 256], mx>.c;
    let Latency = VRGatherVVLat, ReleaseAtCycles = [VRGatherVVOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVRGatherVV", [Interp_VIEU], mx, sew, IsWorstCaseSEW>;
    }
    // For sew == 8, latency is half of the other cases, except for the fractional LMULs (const 4 cycles)
    defvar VRGatherEI16Lat = !if(!eq(sew, 8),
      InterpGetLMULValue<[4, 4, 4, 8, 32, 128, 256], mx>.c,
      InterpGetLMULValue<[4, 4, 4, 4, 16,  64, 256], mx>.c);
    defvar VRGatherEI16Occ = !if(!eq(sew, 8),
      InterpGetLMULValue<[1, 1, 2, 8, 32, 128, 256], mx>.c,
      InterpGetLMULValue<[1, 1, 1, 4, 16,  64, 256], mx>.c);
    let Latency = VRGatherEI16Lat, ReleaseAtCycles = [VRGatherEI16Occ] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVRGatherEI16VV", [Interp_VIEU], mx, sew, IsWorstCaseSEW>;
    }

    defvar VCompressVLat = InterpGetLMULValue<[4, 4, 4, 4, 10, 36, 136], mx>.c;
    defvar VCompressVOcc = InterpGetLMULValue<[1, 1, 1, 3, 10, 36, 136], mx>.c;
    let Latency = VCompressVLat, ReleaseAtCycles = [VCompressVOcc] in {
      defm "" : LMULSEWWriteResMXSEW<"WriteVCompressV", [Interp_VIEU], mx, sew, IsWorstCaseSEW>;
    }
  }
}

// Others
def : WriteRes<WriteCSR, [Interp_IEU]>;
def : WriteRes<WriteNop, [Interp_IEU]>;
def : WriteRes<WriteRdVLENB, [Interp_IEUA]>;

// Assign scheduling info to COPY instructions.
// Note: We try NOT to assign ProcResource but only latency to vector COPY because
// those resources might prevent those COPYs from showing up to the scheulder
// until it's too late.
// Specifically, for a given COPY of live-in (physical) register, ideally we want it
// to be visible to the top available queue as early as possible so that it can be scheduled
// at the beginning of the function. Assigning resource to vector COPYs might risk
// creating structural hazard that prevents those COPYs from even entering the available
// queue and as a consequence, sinking those COPYs.
// I see little difference on assigning ProcResource to scalar COPY or not, so I'm still
// assigning WriteIALU to it.
def InterpCopySchedWriteVariant : SchedWriteVariant<[
  SchedVar<SchedPredicate<[{ TII->isVRegCopy(MI, /*LMUL=*/1) }]>, [InterpWriteVCOPY_M1]>,
  SchedVar<SchedPredicate<[{ TII->isVRegCopy(MI, /*LMUL=*/2) }]>, [InterpWriteVCOPY_M2]>,
  SchedVar<SchedPredicate<[{ TII->isVRegCopy(MI, /*LMUL=*/4) }]>, [InterpWriteVCOPY_M4]>,
  SchedVar<SchedPredicate<[{ TII->isVRegCopy(MI, /*LMUL=*/8) }]>, [InterpWriteVCOPY_M8]>,
  SchedVar<NoSchedPred,                                           [WriteIALU]>
]>;
def : InstRW<[InterpCopySchedWriteVariant], (instrs COPY)>;

//===----------------------------------------------------------------------===//
// Bypass and advance
def : ReadAdvance<ReadJmp, 0>;
def : ReadAdvance<ReadJalr, 0>;
def : ReadAdvance<ReadCSR, 0>;
def : ReadAdvance<ReadStoreData, 0>;
def : ReadAdvance<ReadMemBase, 0>;
def : ReadAdvance<ReadIALU, 0>;
def : ReadAdvance<ReadIALU32, 0>;
def : ReadAdvance<ReadShiftImm, 0>;
def : ReadAdvance<ReadShiftImm32, 0>;
def : ReadAdvance<ReadShiftReg, 0>;
def : ReadAdvance<ReadShiftReg32, 0>;
def : ReadAdvance<ReadIDiv, 0>;
def : ReadAdvance<ReadIDiv32, 0>;
def : ReadAdvance<ReadIRem, 0>;
def : ReadAdvance<ReadIRem32, 0>;
def : ReadAdvance<ReadIMul, 0>;
def : ReadAdvance<ReadIMul32, 0>;
def : ReadAdvance<ReadAtomicWA, 0>;
def : ReadAdvance<ReadAtomicWD, 0>;
def : ReadAdvance<ReadAtomicDA, 0>;
def : ReadAdvance<ReadAtomicDD, 0>;
def : ReadAdvance<ReadAtomicLDW, 0>;
def : ReadAdvance<ReadAtomicLDD, 0>;
def : ReadAdvance<ReadAtomicSTW, 0>;
def : ReadAdvance<ReadAtomicSTD, 0>;
def : ReadAdvance<ReadFStoreData, 0>;
def : ReadAdvance<ReadFMemBase, 0>;
def : ReadAdvance<ReadFAdd16, 0>;
def : ReadAdvance<ReadFAdd32, 0>;
def : ReadAdvance<ReadFAdd64, 0>;
def : ReadAdvance<ReadFMul16, 0>;
def : ReadAdvance<ReadFMA16, 0>;
def : ReadAdvance<ReadFMA16Addend, 0>;
def : ReadAdvance<ReadFMul32, 0>;
def : ReadAdvance<ReadFMul64, 0>;
def : ReadAdvance<ReadFMA32, 0>;
def : ReadAdvance<ReadFMA32Addend, 0>;
def : ReadAdvance<ReadFMA64, 0>;
def : ReadAdvance<ReadFMA64Addend, 0>;
def : ReadAdvance<ReadFDiv16, 0>;
def : ReadAdvance<ReadFDiv32, 0>;
def : ReadAdvance<ReadFDiv64, 0>;
def : ReadAdvance<ReadFSqrt16, 0>;
def : ReadAdvance<ReadFSqrt32, 0>;
def : ReadAdvance<ReadFSqrt64, 0>;
def : ReadAdvance<ReadFCmp16, 0>;
def : ReadAdvance<ReadFCmp32, 0>;
def : ReadAdvance<ReadFCmp64, 0>;
def : ReadAdvance<ReadFSGNJ16, 0>;
def : ReadAdvance<ReadFSGNJ32, 0>;
def : ReadAdvance<ReadFSGNJ64, 0>;
def : ReadAdvance<ReadFMinMax16, 0>;
def : ReadAdvance<ReadFMinMax32, 0>;
def : ReadAdvance<ReadFMinMax64, 0>;
def : ReadAdvance<ReadFCvtF16ToI32, 0>;
def : ReadAdvance<ReadFCvtF16ToI64, 0>;
def : ReadAdvance<ReadFCvtF32ToI32, 0>;
def : ReadAdvance<ReadFCvtF32ToI64, 0>;
def : ReadAdvance<ReadFCvtF64ToI32, 0>;
def : ReadAdvance<ReadFCvtF64ToI64, 0>;
def : ReadAdvance<ReadFCvtI32ToF16, 0>;
def : ReadAdvance<ReadFCvtI32ToF32, 0>;
def : ReadAdvance<ReadFCvtI32ToF64, 0>;
def : ReadAdvance<ReadFCvtI64ToF16, 0>;
def : ReadAdvance<ReadFCvtI64ToF32, 0>;
def : ReadAdvance<ReadFCvtI64ToF64, 0>;
def : ReadAdvance<ReadFCvtF32ToF64, 0>;
def : ReadAdvance<ReadFCvtF64ToF32, 0>;
def : ReadAdvance<ReadFCvtF16ToF32, 0>;
def : ReadAdvance<ReadFCvtF32ToF16, 0>;
def : ReadAdvance<ReadFCvtF16ToF64, 0>;
def : ReadAdvance<ReadFCvtF64ToF16, 0>;
def : ReadAdvance<ReadFMovF16ToI16, 0>;
def : ReadAdvance<ReadFMovI16ToF16, 0>;
def : ReadAdvance<ReadFMovF32ToI32, 0>;
def : ReadAdvance<ReadFMovI32ToF32, 0>;
def : ReadAdvance<ReadFMovF64ToI64, 0>;
def : ReadAdvance<ReadFMovI64ToF64, 0>;
def : ReadAdvance<ReadFClass16, 0>;
def : ReadAdvance<ReadFClass32, 0>;
def : ReadAdvance<ReadFClass64, 0>;

// Bitmanip
def : ReadAdvance<ReadRotateImm, 0>;
def : ReadAdvance<ReadRotateImm32, 0>;
def : ReadAdvance<ReadRotateReg, 0>;
def : ReadAdvance<ReadRotateReg32, 0>;
def : ReadAdvance<ReadCLZ, 0>;
def : ReadAdvance<ReadCLZ32, 0>;
def : ReadAdvance<ReadCTZ, 0>;
def : ReadAdvance<ReadCTZ32, 0>;
def : ReadAdvance<ReadCPOP, 0>;
def : ReadAdvance<ReadCPOP32, 0>;
def : ReadAdvance<ReadORCB, 0>;
def : ReadAdvance<ReadIMinMax, 0>;
def : ReadAdvance<ReadREV8, 0>;
def : ReadAdvance<ReadSHXADD, 0>;
def : ReadAdvance<ReadSHXADD32, 0>;
def : ReadAdvance<ReadCLMUL, 0>;
// Single-bit instructions
def : ReadAdvance<ReadSingleBit, 0>;
def : ReadAdvance<ReadSingleBitImm, 0>;

// 6. Configuration-Setting Instructions
def : ReadAdvance<ReadVSETVLI, 0>;
def : ReadAdvance<ReadVSETVL, 0>;

// 7. Vector Loads and Stores
def : ReadAdvance<ReadVLDX, 0>;
def : ReadAdvance<ReadVSTX, 0>;
defm "" : LMULReadAdvance<"ReadVSTEV", 0>;
defm "" : LMULReadAdvance<"ReadVSTM", 0>;
def : ReadAdvance<ReadVLDSX, 0>;
def : ReadAdvance<ReadVSTSX, 0>;
defm "" : LMULReadAdvance<"ReadVSTS8V", 0>;
defm "" : LMULReadAdvance<"ReadVSTS16V", 0>;
defm "" : LMULReadAdvance<"ReadVSTS32V", 0>;
defm "" : LMULReadAdvance<"ReadVSTS64V", 0>;
defm "" : LMULReadAdvance<"ReadVLDUXV", 0>;
defm "" : LMULReadAdvance<"ReadVLDOXV", 0>;
defm "" : LMULReadAdvance<"ReadVSTUX8", 0>;
defm "" : LMULReadAdvance<"ReadVSTUX16", 0>;
defm "" : LMULReadAdvance<"ReadVSTUX32", 0>;
defm "" : LMULReadAdvance<"ReadVSTUX64", 0>;
defm "" : LMULReadAdvance<"ReadVSTUXV", 0>;
defm "" : LMULReadAdvance<"ReadVSTUX8V", 0>;
defm "" : LMULReadAdvance<"ReadVSTUX16V", 0>;
defm "" : LMULReadAdvance<"ReadVSTUX32V", 0>;
defm "" : LMULReadAdvance<"ReadVSTUX64V", 0>;
defm "" : LMULReadAdvance<"ReadVSTOX8", 0>;
defm "" : LMULReadAdvance<"ReadVSTOX16", 0>;
defm "" : LMULReadAdvance<"ReadVSTOX32", 0>;
defm "" : LMULReadAdvance<"ReadVSTOX64", 0>;
defm "" : LMULReadAdvance<"ReadVSTOXV", 0>;
defm "" : LMULReadAdvance<"ReadVSTOX8V", 0>;
defm "" : LMULReadAdvance<"ReadVSTOX16V", 0>;
defm "" : LMULReadAdvance<"ReadVSTOX32V", 0>;
defm "" : LMULReadAdvance<"ReadVSTOX64V", 0>;
// LMUL Aware
def : ReadAdvance<ReadVST1R, 0>;
def : ReadAdvance<ReadVST2R, 0>;
def : ReadAdvance<ReadVST4R, 0>;
def : ReadAdvance<ReadVST8R, 0>;

// 11. Vector Integer Arithmetic Instructions
defm : LMULReadAdvance<"ReadVIALUV", 0>;
defm : LMULReadAdvance<"ReadVIALUX", 0>;
defm : LMULReadAdvanceW<"ReadVIWALUV", 0>;
defm : LMULReadAdvanceW<"ReadVIWALUX", 0>;
defm : LMULReadAdvance<"ReadVExtV", 0>;
defm : LMULReadAdvance<"ReadVICALUV", 0>;
defm : LMULReadAdvance<"ReadVICALUX", 0>;
defm : LMULReadAdvance<"ReadVShiftV", 0>;
defm : LMULReadAdvance<"ReadVShiftX", 0>;
defm : LMULReadAdvanceW<"ReadVNShiftV", 0>;
defm : LMULReadAdvanceW<"ReadVNShiftX", 0>;
defm : LMULReadAdvance<"ReadVICmpV", 0>;
defm : LMULReadAdvance<"ReadVICmpX", 0>;
defm : LMULReadAdvance<"ReadVIMinMaxV", 0>;
defm : LMULReadAdvance<"ReadVIMinMaxX", 0>;
defm : LMULReadAdvance<"ReadVIMulV", 0>;
defm : LMULReadAdvance<"ReadVIMulX", 0>;
defm : LMULSEWReadAdvance<"ReadVIDivV", 0>;
defm : LMULSEWReadAdvance<"ReadVIDivX", 0>;
defm : LMULReadAdvanceW<"ReadVIWMulV", 0>;
defm : LMULReadAdvanceW<"ReadVIWMulX", 0>;
defm : LMULReadAdvance<"ReadVIMulAddV", 0>;
defm : LMULReadAdvance<"ReadVIMulAddX", 0>;
defm : LMULReadAdvanceW<"ReadVIWMulAddV", 0>;
defm : LMULReadAdvanceW<"ReadVIWMulAddX", 0>;
defm : LMULReadAdvance<"ReadVIMergeV", 0>;
defm : LMULReadAdvance<"ReadVIMergeX", 0>;
defm : LMULReadAdvance<"ReadVIMovV", 0>;
defm : LMULReadAdvance<"ReadVIMovX", 0>;

// 12. Vector Fixed-Point Arithmetic Instructions
defm "" : LMULReadAdvance<"ReadVSALUV", 0>;
defm "" : LMULReadAdvance<"ReadVSALUX", 0>;
defm "" : LMULReadAdvance<"ReadVAALUV", 0>;
defm "" : LMULReadAdvance<"ReadVAALUX", 0>;
defm "" : LMULReadAdvance<"ReadVSMulV", 0>;
defm "" : LMULReadAdvance<"ReadVSMulX", 0>;
defm "" : LMULReadAdvance<"ReadVSShiftV", 0>;
defm "" : LMULReadAdvance<"ReadVSShiftX", 0>;
defm "" : LMULReadAdvanceW<"ReadVNClipV", 0>;
defm "" : LMULReadAdvanceW<"ReadVNClipX", 0>;

// 13. Vector Floating-Point Instructions
defm "" : LMULSEWReadAdvanceF<"ReadVFALUV", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFALUF", 0>;
defm "" : LMULSEWReadAdvanceFW<"ReadVFWALUV", 0>;
defm "" : LMULSEWReadAdvanceFW<"ReadVFWALUF", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFMulV", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFMulF", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFDivV", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFDivF", 0>;
defm "" : LMULSEWReadAdvanceFW<"ReadVFWMulV", 0>;
defm "" : LMULSEWReadAdvanceFW<"ReadVFWMulF", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFMulAddV", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFMulAddF", 0>;
defm "" : LMULSEWReadAdvanceFW<"ReadVFWMulAddV", 0>;
defm "" : LMULSEWReadAdvanceFW<"ReadVFWMulAddF", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFSqrtV", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFRecpV", 0>;
defm "" : LMULReadAdvance<"ReadVFCmpV", 0>;
defm "" : LMULReadAdvance<"ReadVFCmpF", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFMinMaxV", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFMinMaxF", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFSgnjV", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFSgnjF", 0>;
defm "" : LMULReadAdvance<"ReadVFClassV", 0>;
defm "" : LMULReadAdvance<"ReadVFMergeV", 0>;
defm "" : LMULReadAdvance<"ReadVFMergeF", 0>;
defm "" : LMULReadAdvance<"ReadVFMovF", 0>;
defm "" : LMULSEWReadAdvanceF<"ReadVFCvtIToFV", 0>;
defm "" : LMULReadAdvance<"ReadVFCvtFToIV", 0>;
defm "" : LMULSEWReadAdvanceW<"ReadVFWCvtIToFV", 0>;
defm "" : LMULReadAdvanceFW<"ReadVFWCvtFToIV", 0>;
defm "" : LMULSEWReadAdvanceFW<"ReadVFWCvtFToFV", 0>;
defm "" : LMULSEWReadAdvanceFW<"ReadVFNCvtIToFV", 0>;
defm "" : LMULReadAdvanceW<"ReadVFNCvtFToIV", 0>;
defm "" : LMULSEWReadAdvanceFW<"ReadVFNCvtFToFV", 0>;

// 14. Vector Reduction Operations
def : ReadAdvance<ReadVIRedV, 0>;
def : ReadAdvance<ReadVIRedV0, 0>;
def : ReadAdvance<ReadVIWRedV, 0>;
def : ReadAdvance<ReadVIWRedV0, 0>;
def : ReadAdvance<ReadVFRedV, 0>;
def : ReadAdvance<ReadVFRedV0, 0>;
def : ReadAdvance<ReadVFRedOV, 0>;
def : ReadAdvance<ReadVFRedOV0, 0>;
def : ReadAdvance<ReadVFWRedV, 0>;
def : ReadAdvance<ReadVFWRedV0, 0>;
def : ReadAdvance<ReadVFWRedOV, 0>;
def : ReadAdvance<ReadVFWRedOV0, 0>;

// 15. Vector Mask Instructions
defm "" : LMULReadAdvance<"ReadVMALUV", 0>;
defm "" : LMULReadAdvance<"ReadVMPopV", 0>;
defm "" : LMULReadAdvance<"ReadVMFFSV", 0>;
defm "" : LMULReadAdvance<"ReadVMSFSV", 0>;
defm "" : LMULReadAdvance<"ReadVIotaV", 0>;

// 16. Vector Permutation Instructions
def : ReadAdvance<ReadVMovXS, 0>;
def : ReadAdvance<ReadVMovSX_V, 0>;
def : ReadAdvance<ReadVMovSX_X, 0>;
def : ReadAdvance<ReadVMovFS, 0>;
def : ReadAdvance<ReadVMovSF_V, 0>;
def : ReadAdvance<ReadVMovSF_F, 0>;
defm "" : LMULReadAdvance<"ReadVISlideV", 0>;
defm "" : LMULReadAdvance<"ReadVISlideX", 0>;
defm "" : LMULReadAdvance<"ReadVFSlideV", 0>;
defm "" : LMULReadAdvance<"ReadVFSlideF", 0>;
defm "" : LMULSEWReadAdvance<"ReadVRGatherVV_data", 0>;
defm "" : LMULSEWReadAdvance<"ReadVRGatherVV_index", 0>;
defm "" : LMULSEWReadAdvance<"ReadVRGatherEI16VV_data", 0>;
defm "" : LMULSEWReadAdvance<"ReadVRGatherEI16VV_index", 0>;
defm "" : LMULReadAdvance<"ReadVRGatherVX_data", 0>;
defm "" : LMULReadAdvance<"ReadVRGatherVX_index", 0>;
defm "" : LMULReadAdvance<"ReadVRGatherVI_data", 0>;
defm "" : LMULSEWReadAdvance<"ReadVCompressV", 0>;
// LMUL Aware
def : ReadAdvance<ReadVMov1V, 0>;
def : ReadAdvance<ReadVMov2V, 0>;
def : ReadAdvance<ReadVMov4V, 0>;
def : ReadAdvance<ReadVMov8V, 0>;

// Others
def : ReadAdvance<ReadVMask, 0>;
def : ReadAdvance<ReadVPassthru_WorstCase, 0>;
foreach mx = SchedMxList in {
  def : ReadAdvance<!cast<SchedRead>("ReadVPassthru_" # mx), 0>;
  foreach sew = SchedSEWSet<mx>.val in
    def : ReadAdvance<!cast<SchedRead>("ReadVPassthru_" # mx  # "_E" # sew), 0>;
}

//===----------------------------------------------------------------------===//
// Unsupported extensions
defm : UnsupportedSchedQ;
defm : UnsupportedSchedZabha;
defm : UnsupportedSchedZbkb;
defm : UnsupportedSchedZbkx;
defm : UnsupportedSchedZfa;
defm : UnsupportedSchedZvk;
defm : UnsupportedSchedSFB;
defm : UnsupportedSchedXsf;
}
