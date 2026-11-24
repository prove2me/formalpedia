-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_cre_ann_apply
-- name    : GlobalTheory.CompanionTheory.GopEntries.cre_ann_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:39.105338+00:00
-- url     : https://prove2.me/theorems/ba5eec20-eb36-4048-bb02-a467d839c6aa
-- title:
--   Gop Entries: cre ann apply
-- statement:
--   The Gop Entries construction uses the cre ann apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreAnnApply.lean#L57-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreAnnApply.lean#L57-L89

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

theorem GlobalTheory.CompanionTheory.GopEntries.cre_ann_apply {V : Type} [AddCommGroup V] [Module ℂ V] (i j : NC ε) (x : Ch ε V)
    (A : Finset (NC ε)) :
    (cre i * ann j : Module.End ℂ (Ch ε V)) x A = ∑ B, (hh i j A B : ℂ) • x B := by sorry
