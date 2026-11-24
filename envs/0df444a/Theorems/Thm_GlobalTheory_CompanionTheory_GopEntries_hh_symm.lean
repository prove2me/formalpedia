-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_hh_symm
-- name    : GlobalTheory.CompanionTheory.GopEntries.hh_symm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:07.399854+00:00
-- url     : https://prove2.me/theorems/fe3f97f4-233a-4d8d-9626-5014d01e257b
-- title:
--   Gop Entries: hh symm
-- statement:
--   The Gop Entries construction uses the hh symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreAnnApply.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreAnnApply.lean#L45-L49

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

theorem GlobalTheory.CompanionTheory.GopEntries.hh_symm (i j : NC ε) (A B : Finset (NC ε)) : hh i j A B = hh j i B A := by sorry
