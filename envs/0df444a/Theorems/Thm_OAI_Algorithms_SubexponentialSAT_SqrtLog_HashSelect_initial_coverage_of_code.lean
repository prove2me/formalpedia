-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashSelect_initial_coverage_of_code
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.initial_coverage_of_code
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:42:02.471017+00:00
-- url     : https://prove2.me/theorems/ba02baf3-8f5a-44b3-8a03-fb46064d9e2c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.initial_coverage_of_code: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.initial_coverage_of_code` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashSelectTuple.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashSelectTuple.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem initial_coverage_of_code {n m d c : ℕ}
--       (C : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
--       (hcount : (3 * m) ^ d = c + 1) (initial : List (Row m))
--       (hcode : ∀ v : Row m,
--         (∀ r ∈ initial, (∑ e, r e * v e) = 0) → v ≠ 0 →
--         m ≤ d * SparseCode.weight v) :
--       ∀ x, accepts (cnfRowAccept C) initial x = true →
--         0 < HashInput.violationWeight C x →
--         3 * survivingCandidates (cnfRowAccept C) (tupleFamily hcount) x ≤
--           2 * (c + 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.weight` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.Row`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.accepts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.survivingCandidates` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInput.violationWeight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.cnfRowAccept` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.tupleFamily` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Assignment` and `OAI.Algorithms.SubexponentialSAT.SAT.Clause` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history_mass_zero` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashSelectTuple.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.initial_coverage_of_code)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S031

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

theorem initial_coverage_of_code {n m d c : ℕ}
    (C : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (hcount : (3 * m) ^ d = c + 1) (initial : List (Row m))
    (hcode : ∀ v : Row m,
      (∀ r ∈ initial, (∑ e, r e * v e) = 0) → v ≠ 0 →
      m ≤ d * SparseCode.weight v) :
    ∀ x, accepts (cnfRowAccept C) initial x = true →
      0 < HashInput.violationWeight C x →
      3 * survivingCandidates (cnfRowAccept C) (tupleFamily hcount) x ≤
        2 * (c + 1) := by
  sorry

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
end
