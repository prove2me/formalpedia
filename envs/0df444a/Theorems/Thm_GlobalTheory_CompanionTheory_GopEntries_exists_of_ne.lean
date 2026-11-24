-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_exists_of_ne
-- name    : GlobalTheory.CompanionTheory.GopEntries.exists_of_ne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:19.932884+00:00
-- url     : https://prove2.me/theorems/288d101b-90ce-4edd-a9c9-922efc2e87b3
-- title:
--   Gop Entries: exists of ne
-- statement:
--   The Gop Entries construction uses the exists of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreAnnApply.lean#L122-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreAnnApply.lean#L122-L132

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

theorem GlobalTheory.CompanionTheory.GopEntries.exists_of_ne {c d : Fin n} {A B : Finset (NC ε)} (h : gg c d A B ≠ 0) :
    ∃ i j : NC ε, ((i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2) ∨ (i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1)) ∧
      i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j := by sorry
