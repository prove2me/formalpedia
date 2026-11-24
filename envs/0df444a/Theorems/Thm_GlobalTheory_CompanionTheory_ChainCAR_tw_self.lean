-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_tw_self
-- name    : GlobalTheory.CompanionTheory.ChainCAR.tw_self
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:32:59.348844+00:00
-- url     : https://prove2.me/theorems/7b9183a7-3ee3-49a2-810d-0ebf7e80585a
-- title:
--   Chain CAR: tw self
-- statement:
--   The Chain CAR construction uses the tw self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreApply.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreApply.lean#L28-L28

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

theorem GlobalTheory.CompanionTheory.ChainCAR.tw_self (i : NC ε) : tw i i = 1 := by sorry
