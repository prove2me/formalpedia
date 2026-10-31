-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Scalar_negative_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.negative_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:11:45.637286+00:00
-- url     : https://prove2.me/theorems/6a300672-b43d-4c16-9b26-4f8e75e5f187
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.negative_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.negative_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramScalarSteps.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramScalarSteps.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram`, `open CRTLocalProgram (ServiceSpec)`):
--
--   ```lean
--   theorem negative_run {C : Type*} (encode : C → List Bool) (multiply : Cmd 16 256)
--       (mulOp : C → C → C) (K W : ℕ) (d : Data) (node minusOne : C)
--       (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp K)
--       (hw : ∀ a, (encode a).length = W)
--       (hn : d.stacks 259 = encode node) (hminus : d.stacks 211 = encode minusOne)
--       (h263 : d.stacks 263 = []) (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
--       ∃ n ≤ K + 26 * W + 26, ∃ rf, Eval (negative multiply) n d
--         ⟨rf, Function.update d.stacks 263 (encode (mulOp node minusOne))⟩
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.localPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.cleanPorts` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.ServiceSpec` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.negative` (definitions bundle `OAIQ081S144` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramScalarSteps.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.negative_run)

import Mathlib
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec)

theorem negative_run {C : Type*} (encode : C → List Bool) (multiply : Cmd 16 256)
    (mulOp : C → C → C) (K W : ℕ) (d : Data) (node minusOne : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp K)
    (hw : ∀ a, (encode a).length = W)
    (hn : d.stacks 259 = encode node) (hminus : d.stacks 211 = encode minusOne)
    (h263 : d.stacks 263 = []) (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
    ∃ n ≤ K + 26 * W + 26, ∃ rf, Eval (negative multiply) n d
      ⟨rf, Function.update d.stacks 263 (encode (mulOp node minusOne))⟩ := by
  sorry

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

end OAI.Algorithms
end
