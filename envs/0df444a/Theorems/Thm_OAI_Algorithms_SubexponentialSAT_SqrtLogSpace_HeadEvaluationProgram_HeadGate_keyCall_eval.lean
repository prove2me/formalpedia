-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram_HeadGate_keyCall_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate.keyCall_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:46:59.197068+00:00
-- url     : https://prove2.me/theorems/476637ce-1cd6-478a-9dac-42c16faff75d
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate.keyCall_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate.keyCall_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadEvaluationProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadEvaluationProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate`, with `open OAI BitProgram StructuredCalls`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram`, `open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport`):
--
--   ```lean
--   theorem keyCall_eval (regs : Fin 16 → Bool) (W bits : List Bool)
--       (rows : List (List (List Bool))) (key wanted E H : List Bool)
--       (hlen : ∀ row ∈ rows, row.length=bits.length) :
--       ∃ n ≤ AttainedSignatureProgram.cost W bits rows+1, ∃ out,
--         Eval keyCall n (state regs W bits rows key wanted E H)
--           (state out W bits rows (signatureValue W bits rows++key) wanted E H)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signatureValue` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.cost` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate.keyCall` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate.state` (definitions bundle `OAIQ081S136` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadEvaluationProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate.keyCall_eval)

import Mathlib
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

theorem keyCall_eval (regs : Fin 16 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key wanted E H : List Bool)
    (hlen : ∀ row ∈ rows, row.length=bits.length) :
    ∃ n ≤ AttainedSignatureProgram.cost W bits rows+1, ∃ out,
      Eval keyCall n (state regs W bits rows key wanted E H)
        (state out W bits rows (signatureValue W bits rows++key) wanted E H) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate
end
