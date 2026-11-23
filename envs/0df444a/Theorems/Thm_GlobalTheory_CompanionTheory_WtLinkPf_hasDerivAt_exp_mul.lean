-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_hasDerivAt_exp_mul
-- name    : GlobalTheory.CompanionTheory.WtLinkPf.hasDerivAt_exp_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:51.030947+00:00
-- url     : https://prove2.me/theorems/65d6f29b-92f6-441c-8fc9-21e63c2c95ab
-- title:
--   Wt Link Pf: has Deriv At exp mul
-- statement:
--   The Wt Link Pf construction uses the has Deriv At exp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L98-L101

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

theorem GlobalTheory.CompanionTheory.WtLinkPf.hasDerivAt_exp_mul (c : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c)) (Complex.exp ((s : ℂ) * c) * c) s := by sorry
