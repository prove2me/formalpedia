-- Prove2me | Theorems.Thm_GlobalTheory_T_quadratic_le_log_sum_exp_of_bounded_centred
-- name    : GlobalTheory.T.quadratic_le_log_sum_exp_of_bounded_centred
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:55:56.819263+00:00
-- url     : https://prove2.me/theorems/e1d74321-a02a-42a1-ace4-5006b4f19cbb
-- title:
--   T: quadratic le log sum exp of bounded centred
-- statement:
--   The T construction uses the quadratic le log sum exp of bounded centred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CumulantLowerBoundOfBoundedCentredStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CumulantLowerBoundOfBoundedCentredStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CumulantLowerBoundOfBoundedCentred
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CumulantLowerBoundOfBoundedCentredStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.quadratic_le_log_sum_exp_of_bounded_centred : ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (R : ℝ), 0 < R → (∀ J, 0 ≤ w J) → ∑ J, w J = 1 → ∑ J, w J * y J = 0 → (∀ J, w J ≠ 0 → |y J| ≤ R) → min 1 (1 / R) * (∑ J, w J * y J ^ 2) / 4 ≤ Real.log (∑ J, w J * Real.exp (y J)) := by sorry
