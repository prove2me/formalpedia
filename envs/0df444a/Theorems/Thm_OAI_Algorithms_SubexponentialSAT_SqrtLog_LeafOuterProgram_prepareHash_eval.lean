-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafOuterProgram_prepareHash_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.prepareHash_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:03:38.587293+00:00
-- url     : https://prove2.me/theorems/81750991-1c57-4f5b-bab6-d4d3b00b8c29
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.prepareHash_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.prepareHash_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafOuterProgramPrepare.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafOuterProgramPrepare.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage`):
--
--   ```lean
--   theorem prepareHash_eval (a : Data) (L : ℕ) (hW : WordBound L a)
--       (hr : Execution.HashInputs.Ready (projectState
--         LeafProgram.HashParameters.ports.hash.register LeafProgram.HashParameters.ports.hash.stack a))
--       (hm : BinaryArithmetic.toNat (a.stacks 782) ≠ 0) (ht : a.stacks 767=[]) :
--       ∃ t ≤ prepareHashBudget L, ∃ b,
--         Eval prepareHash t a b ∧ WorkerEmpty b ∧
--         Execution.HashInputs.Ready (projectState
--           LeafProgram.HashParameters.ports.hash.register LeafProgram.HashParameters.ports.hash.stack b) ∧
--         BinaryArithmetic.toNat (b.stacks 768)=3*BinaryArithmetic.toNat (a.stacks 782) ∧
--         BinaryArithmetic.toNat (b.stacks 773)=SparseCode.distanceDenom
--           (BinaryArithmetic.toNat (a.stacks 782)) (BinaryArithmetic.toNat (a.stacks 786)) ∧
--         BinaryArithmetic.toNat (b.stacks 774)=HashSelect.loopCap
--           (BinaryArithmetic.toNat (a.stacks 785)) (BinaryArithmetic.toNat (a.stacks 782)) ∧
--         b.stacks 777=a.stacks 777 ∧
--         (∀ i : Fin 896, 782 ≤ i.val → b.stacks i=a.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.Hash.Ports` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.prepareHashBudget` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.Ports.hash` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.HashParameters.ports` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashInputs.Ready` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.WorkerEmpty` (definitions bundle `OAIQ081S108` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.prepareHash` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.start_trace_space` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafOuterProgramPrepare.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.prepareHash_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem prepareHash_eval (a : Data) (L : ℕ) (hW : WordBound L a)
    (hr : Execution.HashInputs.Ready (projectState
      LeafProgram.HashParameters.ports.hash.register LeafProgram.HashParameters.ports.hash.stack a))
    (hm : BinaryArithmetic.toNat (a.stacks 782) ≠ 0) (ht : a.stacks 767=[]) :
    ∃ t ≤ prepareHashBudget L, ∃ b,
      Eval prepareHash t a b ∧ WorkerEmpty b ∧
      Execution.HashInputs.Ready (projectState
        LeafProgram.HashParameters.ports.hash.register LeafProgram.HashParameters.ports.hash.stack b) ∧
      BinaryArithmetic.toNat (b.stacks 768)=3*BinaryArithmetic.toNat (a.stacks 782) ∧
      BinaryArithmetic.toNat (b.stacks 773)=SparseCode.distanceDenom
        (BinaryArithmetic.toNat (a.stacks 782)) (BinaryArithmetic.toNat (a.stacks 786)) ∧
      BinaryArithmetic.toNat (b.stacks 774)=HashSelect.loopCap
        (BinaryArithmetic.toNat (a.stacks 785)) (BinaryArithmetic.toNat (a.stacks 782)) ∧
      b.stacks 777=a.stacks 777 ∧
      (∀ i : Fin 896, 782 ≤ i.val → b.stacks i=a.stacks i) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end
