-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_gg_diag
-- name    : GlobalTheory.CompanionTheory.GopEntries.gg_diag
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:43:52.036472+00:00
-- url     : https://prove2.me/theorems/cc157b69-23cc-4efa-b035-1d690c3e7c1b
-- title:
--   Gop Entries: gg diag
-- statement:
--   The Gop Entries construction uses the gg diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreAnnApply.lean#L134-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreAnnApply.lean#L134-L163

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

theorem GlobalTheory.CompanionTheory.GopEntries.gg_diag (c : Fin n) (A B : Finset (NC ε)) : gg c c A B = if A = B then wtA A c else 0 := by sorry
