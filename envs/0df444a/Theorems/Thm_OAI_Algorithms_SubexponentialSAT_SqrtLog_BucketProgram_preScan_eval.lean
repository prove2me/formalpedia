-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_BucketProgram_preScan_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preScan_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:57:40.125174+00:00
-- url     : https://prove2.me/theorems/b65df79e-cc5d-4841-91c9-57d52259550f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preScan_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preScan_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/BucketProgramPreprocessRow.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/BucketProgramPreprocessRow.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport`):
--
--   ```lean
--   theorem preScan_eval (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord) :
--       ∃ t ≤ preScanCost W xs+1, ∃ rf ys,
--         Eval preScan t (preState regs W xs [])
--           (preState rf W [] (words ys.reverse)) ∧ List.Forall₂ (shiftedWord W) xs ys
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.SignedWord` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preScanCost` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.shiftedWord` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preScan` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preState` (definitions bundle `OAIQ081S082` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixProgram_runsIn` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/BucketProgramPreprocessRow.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preScan_eval)

import Mathlib
import Definitions.Def_OAIQ081S082

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem preScan_eval (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord) :
    ∃ t ≤ preScanCost W xs+1, ∃ rf ys,
      Eval preScan t (preState regs W xs [])
        (preState rf W [] (words ys.reverse)) ∧ List.Forall₂ (shiftedWord W) xs ys := by
  sorry

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end
