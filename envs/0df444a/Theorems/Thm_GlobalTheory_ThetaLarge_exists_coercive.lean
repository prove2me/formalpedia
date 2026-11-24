-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLarge_exists_coercive
-- name    : GlobalTheory.ThetaLarge.exists_coercive
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:06:32.921623+00:00
-- url     : https://prove2.me/theorems/fb626a11-2b77-43fe-85ba-0ae59eff3ac5
-- title:
--   Theta Large: exists coercive
-- statement:
--   The Theta Large construction uses the exists coercive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsThetaSeriesApplyNeZeroOfLargeForm.lean#L152-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsThetaSeriesApplyNeZeroOfLargeForm.lean#L152-L170

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
variable {g : ℕ}

theorem GlobalTheory.ThetaLarge.exists_coercive (M : Matrix (Fin g) (Fin g) ℂ)
    (hM : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ M.mulVec (star z)).re) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : Fin g → ℂ, c * ‖z‖ ^ 2 ≤ (z ⬝ᵥ M.mulVec (star z)).re := by sorry
