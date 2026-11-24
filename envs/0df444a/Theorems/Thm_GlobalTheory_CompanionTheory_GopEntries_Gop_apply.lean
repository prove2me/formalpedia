-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_Gop_apply
-- name    : GlobalTheory.CompanionTheory.GopEntries.Gop_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:00.463915+00:00
-- url     : https://prove2.me/theorems/c8288b08-d0cb-48d0-9b70-9a7e0e560031
-- title:
--   Gop Entries: Gop apply
-- statement:
--   The Gop Entries construction uses the Gop apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreAnnApply.lean#L91-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreAnnApply.lean#L91-L105

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

theorem GlobalTheory.CompanionTheory.GopEntries.Gop_apply {V : Type} [AddCommGroup V] [Module ℂ V] (c d : Fin n) (x : Ch ε V)
    (A : Finset (NC ε)) : Gop ε c d x A = ∑ B, (gg c d A B : ℂ) • x B := by sorry
