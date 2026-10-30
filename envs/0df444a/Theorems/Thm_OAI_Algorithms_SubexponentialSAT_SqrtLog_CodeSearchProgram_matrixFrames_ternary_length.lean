-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_matrixFrames_ternary_length
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames_ternary_length
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:46:22.104518+00:00
-- url     : https://prove2.me/theorems/197ce4e9-103f-4012-b50b-18130639ac29
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames_ternary_length: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames_ternary_length` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram`, with `open SubexponentialSAT.Subexp`):
--
--   ```lean
--   theorem matrixFrames_ternary_length {t D : ℕ}
--       (Q : Fin t → Fin D → SparseCode.F3) : (matrixFrames Q).length = 5 * (t * D)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.F3` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames` (definitions bundle `OAIQ081S050` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordInput_length_le` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames_ternary_length)

import Mathlib
import Definitions.Def_OAIQ081S050

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.Subexp

theorem matrixFrames_ternary_length {t D : ℕ}
    (Q : Fin t → Fin D → SparseCode.F3) : (matrixFrames Q).length = 5 * (t * D) := by
  sorry

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end
