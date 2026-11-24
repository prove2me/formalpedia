-- Prove2me | Theorems.Thm_GlobalTheory_norm_sq_add_sum_Iio_le
-- name    : GlobalTheory.norm_sq_add_sum_Iio_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:12:53.147541+00:00
-- url     : https://prove2.me/theorems/e2058119-cbd5-45f3-ba9b-6e174e9cbd64
-- title:
--   Global Theory: norm sq add sum Iio le
-- statement:
--   The Global Theory construction uses the norm sq add sum Iio le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsShortBasisAdaptedOfSubsetSpan.lean#L170-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsShortBasisAdaptedOfSubsetSpan.lean#L170-L178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem GlobalTheory.norm_sq_add_sum_Iio_le {n : ℕ} {v : Fin n → E} {i : Fin n} {r : ℝ}
    (h : ∀ j ≤ i, ‖v j‖ ≤ r) :
    ‖v i‖ ^ 2 + (1 / 4) * ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 ≤ (((i : ℕ) + 1 + 3 : ℝ) / 4) * r ^ 2 := by sorry
