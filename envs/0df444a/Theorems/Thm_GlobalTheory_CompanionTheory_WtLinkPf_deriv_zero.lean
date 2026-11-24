-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_deriv_zero
-- name    : GlobalTheory.CompanionTheory.WtLinkPf.deriv_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:38:39.618699+00:00
-- url     : https://prove2.me/theorems/7a0734f7-bc9c-47fe-92d1-d304e8b6e68b
-- title:
--   Wt Link Pf: deriv zero
-- statement:
--   The Wt Link Pf construction uses the deriv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L90-L96

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExpMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WtLinkPf
open PI.UpqRep
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem GlobalTheory.CompanionTheory.WtLinkPf.deriv_zero {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ S} (h : CompanionTheory.D.DSIC.IsSmMod ε σ S E) (θ : Fin n → ℝ) (v : S) :
    HasDerivAt (fun t : ℝ => σ (tor (t • θ)) v) (∑ a, ((θ a : ℂ) * Complex.I) • (E a a v : H)) 0 := by sorry
