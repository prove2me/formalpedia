-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_key_inj
-- name    : GlobalTheory.CompanionTheory.ChainCAR.key_inj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:32:28.344368+00:00
-- url     : https://prove2.me/theorems/eb18f22f-b38f-4edd-9aa1-14de7fd10b18
-- title:
--   Chain CAR: key inj
-- statement:
--   The Chain CAR construction uses the key inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreApply.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreApply.lean#L13-L24

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

theorem GlobalTheory.CompanionTheory.ChainCAR.key_inj {i j : NC ε} (h : key i = key j) : i = j := by sorry
