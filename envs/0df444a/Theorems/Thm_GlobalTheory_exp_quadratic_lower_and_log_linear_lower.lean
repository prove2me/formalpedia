-- Prove2me | Theorems.Thm_GlobalTheory_exp_quadratic_lower_and_log_linear_lower
-- name    : GlobalTheory.exp_quadratic_lower_and_log_linear_lower
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:07.812304+00:00
-- url     : https://prove2.me/theorems/2c08c27f-2fbf-41de-9d00-4b8152017029
-- title:
--   Global Theory: exp quadratic lower and log linear lower
-- statement:
--   The Global Theory construction uses the exp quadratic lower and log linear lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExpQuadraticLowerAndLogLinearLower.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExpQuadraticLowerAndLogLinearLower.lean#L32-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpQuadraticLowerAndLogLinearLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
open GlobalTheory

theorem GlobalTheory.exp_quadratic_lower_and_log_linear_lower :
    (∀ u : ℝ, |u| ≤ 1 → 1 + u + u ^ 2 / 3 ≤ Real.exp u) ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 3 → 3 * u / 4 ≤ Real.log (1 + u) := by sorry
