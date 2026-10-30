-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_BucketProgram_preMatrixProgram_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixProgram_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:57:46.407886+00:00
-- url     : https://prove2.me/theorems/6b3ad718-8374-4550-a27d-135eaa0b4051
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixProgram_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixProgram_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/BucketProgramPreprocessMatrix.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/BucketProgramPreprocessMatrix.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport`):
--
--   ```lean
--   theorem preMatrixProgram_runsIn (regs : Fin 8 → Bool) (W : List Bool)
--       (rows : List (List SignedWord)) :
--       ∃ rf ys, RunsIn preMatrixProgram (preMatrixCost W rows+1)
--         ((preMatrixState regs W rows []).withPC (some preMatrixProgram.entry))
--         ((preMatrixState rf W [] (words (ys.map words))).withPC none) ∧
--         List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.SignedWord` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.shiftedWord` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixProgram` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixState` (definitions bundle `OAIQ081S082` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.shift_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/BucketProgramPreprocessMatrix.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixProgram_runsIn)

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

theorem preMatrixProgram_runsIn (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) :
    ∃ rf ys, RunsIn preMatrixProgram (preMatrixCost W rows+1)
      ((preMatrixState regs W rows []).withPC (some preMatrixProgram.entry))
      ((preMatrixState rf W [] (words (ys.map words))).withPC none) ∧
      List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys := by
  sorry

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end
