-- Prove2me | Theorems.Thm_GlobalTheory_SectionsCommRing_Sections_equiv_apply
-- name    : GlobalTheory.SectionsCommRing.Sections.equiv_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:58.432274+00:00
-- url     : https://prove2.me/theorems/7bc39254-4dd2-4473-a2f7-a247284db913
-- title:
--   Sections: equiv apply
-- statement:
--   The Sections construction uses the equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/StructureHomApply.lean#L37-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/StructureHomApply.lean#L37-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.SectionsCommRing
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
open GlobalTheory.SectionsCommRing.Sections
variable (s : X ⟶ Spec (CommRingCat.of R))

theorem GlobalTheory.SectionsCommRing.Sections.equiv_apply (U : X.Opens) (a : Sections s U) : equiv s U a = a := by sorry
