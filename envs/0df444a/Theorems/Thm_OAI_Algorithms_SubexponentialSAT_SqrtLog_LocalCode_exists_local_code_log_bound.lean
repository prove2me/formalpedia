-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LocalCode_exists_local_code_log_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.exists_local_code_log_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:49:37.50562+00:00
-- url     : https://prove2.me/theorems/a6fb655d-b656-4121-a622-6a97f902df12
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.exists_local_code_log_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.exists_local_code_log_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LocalCodeLogBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LocalCodeLogBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode`, with `open SparseCode`):
--
--   ```lean
--   theorem exists_local_code_log_bound (D B ell t : ℕ)
--       (hB : 0 < B) (hell : 0 < ell) (hD : D ≤ 2 ^ ell)
--       (ht : D ≤ 8 * B * t) :
--       ∃ Q : CheckMatrix (Fin t) (Fin D),
--         HasDistance Q (D / (100 * B * ell) + 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.CheckMatrix` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.HasDistance` (definitions bundle `OAIQ081S060` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.graph_call` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.local_call` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LocalCodeLogBound.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.exists_local_code_log_bound)

import Mathlib
import Definitions.Def_OAIQ081S060

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableHasDistance _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LocalCode

open SparseCode

theorem exists_local_code_log_bound (D B ell t : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hD : D ≤ 2 ^ ell)
    (ht : D ≤ 8 * B * t) :
    ∃ Q : CheckMatrix (Fin t) (Fin D),
      HasDistance Q (D / (100 * B * ell) + 1) := by
  sorry

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
end
