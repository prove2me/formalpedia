-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_exists_least_norm_unique
-- name    : GlobalTheory.CompanionTheory.RgFl.exists_least_norm_unique
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:55.045812+00:00
-- url     : https://prove2.me/theorems/0c31d7d2-c013-42ab-bfcd-3b65b470b679
-- title:
--   Rg Fl: exists least norm unique
-- statement:
--   The Rg Fl construction uses the exists least norm unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FixedVectorStatement.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FixedVectorStatement.lean#L8-L35

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FixedVectorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl

theorem GlobalTheory.CompanionTheory.RgFl.exists_least_norm_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {C : Set E} (hne : C.Nonempty) (hcl : IsClosed C) (hconv : Convex ℝ C) :
    ∃ u ∈ C, ∀ w ∈ C, ‖u‖ ≤ ‖w‖ ∧ (‖w‖ ≤ ‖u‖ → w = u) := by sorry
