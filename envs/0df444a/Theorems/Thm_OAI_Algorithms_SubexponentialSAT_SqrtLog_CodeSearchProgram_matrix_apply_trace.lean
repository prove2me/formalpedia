-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_matrix_apply_trace
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrix_apply_trace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:52:34.822188+00:00
-- url     : https://prove2.me/theorems/93ac83ed-dfbf-4c56-99a4-4ba4bbef105e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrix_apply_trace: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrix_apply_trace` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramMatrix.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramMatrix.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.Subexp`, `open scoped BigOperators`):
--
--   ```lean
--   theorem matrix_apply_trace {p t D : ℕ} [Fact p.Prime]
--       (Q : Fin t → Fin D → ZMod p) (x : Fin D → ZMod p) (regs : Fin 8 → Bool) :
--       ∃ n rf, n ≤ MatrixVectorProgram.matrixBudget t D (MatrixWordEncoding.width p) ∧
--         Trace MatrixVectorProgram.matrixProgram n
--           ((matrixInput Q x regs).withPC (some MatrixVectorProgram.matrixProgram.entry))
--           ((matrixOutput Q x rf).withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrixBudget` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordEncoding.width` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixInput` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixOutput` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrixCommand` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrixProgram` (definitions bundle `OAIQ081S069` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCounts_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramMatrix.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrix_apply_trace)

import Mathlib
import Definitions.Def_OAIQ081S069

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp
open scoped BigOperators

theorem matrix_apply_trace {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) (x : Fin D → ZMod p) (regs : Fin 8 → Bool) :
    ∃ n rf, n ≤ MatrixVectorProgram.matrixBudget t D (MatrixWordEncoding.width p) ∧
      Trace MatrixVectorProgram.matrixProgram n
        ((matrixInput Q x regs).withPC (some MatrixVectorProgram.matrixProgram.entry))
        ((matrixOutput Q x rf).withPC none) := by
  sorry

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end
