-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_sgR_mul_self
-- name    : GlobalTheory.CompanionTheory.GopEntries.sgR_mul_self
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:48.838437+00:00
-- url     : https://prove2.me/theorems/3845a251-37a1-4d86-a8e8-d0ad68110999
-- title:
--   Gop Entries: sg R mul self
-- statement:
--   The Gop Entries construction uses the sg R mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreAnnApply.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreAnnApply.lean#L41-L43

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreAnnApply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GopEntries
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool}

theorem GlobalTheory.CompanionTheory.GopEntries.sgR_mul_self (i : NC ε) (A : Finset (NC ε)) : sgR i A * sgR i A = 1 := by sorry
