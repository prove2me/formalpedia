-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_sg_mul_self
-- name    : GlobalTheory.CompanionTheory.ChainCAR.sg_mul_self
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:33:42.922458+00:00
-- url     : https://prove2.me/theorems/84541d3b-dbda-4446-880f-9476b33c4846
-- title:
--   Chain CAR: sg mul self
-- statement:
--   The Chain CAR construction uses the sg mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreApply.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreApply.lean#L40-L42

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ChainCAR
variable {n : ℕ} {ε : Fin n → Bool}

theorem GlobalTheory.CompanionTheory.ChainCAR.sg_mul_self (i : NC ε) (A : Finset (NC ε)) : sg i A * sg i A = 1 := by sorry
