-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_one_param
-- name    : GlobalTheory.CompanionTheory.WtLinkPf.one_param
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:25:03.484092+00:00
-- url     : https://prove2.me/theorems/354b3c3c-de31-49ee-8a4a-f0147cd3e5d5
-- title:
--   Wt Link Pf: one param
-- statement:
--   The Wt Link Pf construction uses the one param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L103-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L103-L135

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

theorem GlobalTheory.CompanionTheory.WtLinkPf.one_param (φ : ℝ → (H →L[ℂ] H)) (hadd : ∀ s t, φ (s + t) = φ s * φ t) (h0 : φ 0 = 1) (v : H) (c : ℂ)
    (hd : HasDerivAt (fun t => φ t v) (c • v) 0) : φ 1 v = Complex.exp c • v := by sorry
