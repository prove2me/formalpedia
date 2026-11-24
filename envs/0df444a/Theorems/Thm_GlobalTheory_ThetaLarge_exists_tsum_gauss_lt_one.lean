-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLarge_exists_tsum_gauss_lt_one
-- name    : GlobalTheory.ThetaLarge.exists_tsum_gauss_lt_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:06:15.735802+00:00
-- url     : https://prove2.me/theorems/f234fc73-195f-4e2d-a0cd-4e2a1d653701
-- title:
--   Theta Large: exists tsum gauss lt one
-- statement:
--   The Theta Large construction uses the exists tsum gauss lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsThetaSeriesApplyNeZeroOfLargeForm.lean#L16-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsThetaSeriesApplyNeZeroOfLargeForm.lean#L16-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsThetaSeriesApplyNeZeroOfLargeForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ThetaLarge
variable {E : Type*} [NormedAddCommGroup E]

theorem GlobalTheory.ThetaLarge.exists_tsum_gauss_lt_one [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [DecidableEq L] :
    ∃ a : ℝ, 0 < a ∧ ∑' l : L, (if l = 0 then 0 else Real.exp (-a * ‖(l : E)‖ ^ 2)) < 1 := by sorry
