-- Prove2me | Theorems.Thm_GlobalTheory_Kempf_interSheaf_map_hom_app
-- name    : GlobalTheory.Kempf.interSheaf_map_hom_app
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:46.06401+00:00
-- url     : https://prove2.me/theorems/74c1f975-f95f-4043-b976-c2fb571add44
-- title:
--   Kempf: inter Sheaf map hom app
-- statement:
--   The Kempf construction uses the inter Sheaf map hom app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L59-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Opposite TopologicalSpace
universe w u v' u'
noncomputable section
open GlobalTheory
open GlobalTheory.Kempf
variable {X : TopCat.{u}}
variable (A : Type u') [Category.{v'} A]
variable {A}

theorem GlobalTheory.Kempf.interSheaf_map_hom_app (W : Opens X) {F G : X.Sheaf A} (f : F ⟶ G) (B : Opens X) :
    ((interSheaf A W).map f).hom.app (op B) = f.hom.app (op (B ⊓ W)) := by sorry

attribute [defeq] GlobalTheory.Kempf.interSheaf_map_hom_app
