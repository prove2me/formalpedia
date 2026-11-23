-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_star_exp_mul
-- name    : GlobalTheory.CompanionTheory.WtLinkPf.star_exp_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:12.191939+00:00
-- url     : https://prove2.me/theorems/dcdc43a8-cacc-443a-9e12-c032aaadf5b3
-- title:
--   Wt Link Pf: star exp mul
-- statement:
--   The Wt Link Pf construction uses the star exp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L33-L35

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

theorem GlobalTheory.CompanionTheory.WtLinkPf.star_exp_mul (x : ℝ) : star (Complex.exp ((x : ℂ) * Complex.I)) * Complex.exp ((x : ℂ) * Complex.I) = 1 := by sorry
