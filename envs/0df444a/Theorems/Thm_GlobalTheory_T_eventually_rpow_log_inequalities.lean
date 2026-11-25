-- Prove2me | Theorems.Thm_GlobalTheory_T_eventually_rpow_log_inequalities
-- name    : GlobalTheory.T.eventually_rpow_log_inequalities
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:45.842284+00:00
-- url     : https://prove2.me/theorems/f86d2a66-1c3e-460f-bdb6-bf80f029f339
-- title:
--   T: eventually rpow log inequalities
-- statement:
--   The T construction uses the eventually rpow log inequalities property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiveElementaryInequalitiesEventuallyStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiveElementaryInequalitiesEventuallyStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiveElementaryInequalitiesEventually
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiveElementaryInequalitiesEventuallyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eventually_rpow_log_inequalities : ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ᶠ x : ℝ in Filter.atTop, x ^ (eps / 4) + x ^ (eps / 3) + 1 + 3 * Real.log x ≤ x ^ eps / 5 ∧ 11 ≤ x ^ (eps / 5) ∧ 8 * Real.log x ^ 2 < x ^ 2 ∧ 2 * x ^ (eps / 5 + eps / 100) ≤ Real.sqrt (x * x ^ (-(eps / 8))) ∧ 44 ≤ Real.sqrt (x * x ^ (-(eps / 8))) := by sorry
