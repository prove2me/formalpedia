-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_wtA_eq
-- name    : GlobalTheory.CompanionTheory.DSNormLt.wtA_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:36:17.749839+00:00
-- url     : https://prove2.me/theorems/c60c3c96-ab39-4c97-8255-60901900e643
-- title:
--   DSNorm Lt: wt A eq
-- statement:
--   The DSNorm Lt construction uses the wt A eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L102-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L102-L140

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.DSNormLt.wtA_eq {ε : Fin n → Bool} (A : Finset (NC ε)) (c : Fin n) :
    wtA A c = ∑ b, (ind A c b - ind A b c) := by sorry
