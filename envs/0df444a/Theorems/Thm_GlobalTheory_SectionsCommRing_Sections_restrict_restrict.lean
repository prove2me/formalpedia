-- Prove2me | Theorems.Thm_GlobalTheory_SectionsCommRing_Sections_restrict_restrict
-- name    : GlobalTheory.SectionsCommRing.Sections.restrict_restrict
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:55.763708+00:00
-- url     : https://prove2.me/theorems/773c7d1f-6165-55b3-8c90-64fa7ed18d1e
-- title:
--   Sections: restrict restrict
-- statement:
--   The Sections construction uses the restrict restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/StructureHomApply.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/StructureHomApply.lean#L43-L48

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

theorem GlobalTheory.SectionsCommRing.Sections.restrict_restrict {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (a : Sections s U) :
    restrict s k (restrict s h a) = restrict s (k.trans h) a := by sorry
