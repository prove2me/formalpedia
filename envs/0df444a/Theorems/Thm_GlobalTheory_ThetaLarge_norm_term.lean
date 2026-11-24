-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLarge_norm_term
-- name    : GlobalTheory.ThetaLarge.norm_term
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:06:30.40471+00:00
-- url     : https://prove2.me/theorems/e936e432-ac8d-493e-9048-46a1225f543b
-- title:
--   Theta Large: norm term
-- statement:
--   The Theta Large construction uses the norm term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsThetaSeriesApplyNeZeroOfLargeForm.lean#L64-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsThetaSeriesApplyNeZeroOfLargeForm.lean#L64-L78

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
variable {L : Submodule ℤ E} {H : E → E → ℂ} {χ : L → ℂ}

theorem GlobalTheory.ThetaLarge.norm_term (hl : ∀ x y w, H (x + y) w = H x w + H y w)
    (hr : ∀ x y w, H w (x + y) = H w x + H w y) (hs : ∀ x y, H y x = (starRingEnd ℂ) (H x y))
    (h1 : ∀ l, ‖χ l‖ = 1) (z₀ : E) (l : L) (z : E) :
    ‖term L H χ z₀ l z‖ = Real.exp (π / 2 * ((H z z).re + (H z₀ z₀).re)) *
      Real.exp (-(π / 2) * (H (l + (z - z₀)) (l + (z - z₀))).re) := by sorry
