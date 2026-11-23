-- Prove2me | Theorems.Thm_GlobalTheory_Kempf_interSheaf_obj_obj_obj
-- name    : GlobalTheory.Kempf.interSheaf_obj_obj_obj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:48.415288+00:00
-- url     : https://prove2.me/theorems/ef3f9f57-af3e-44b7-9011-0b6c37b6ddfe
-- title:
--   Kempf: inter Sheaf obj obj obj
-- statement:
--   The Kempf construction uses the inter Sheaf obj obj obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L52-L53

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

theorem GlobalTheory.Kempf.interSheaf_obj_obj_obj (W : Opens X) (F : X.Sheaf A) (B : Opens X) :
    ((interSheaf A W).obj F).obj.obj (op B) = F.obj.obj (op (B ⊓ W)) := by sorry

attribute [defeq] GlobalTheory.Kempf.interSheaf_obj_obj_obj
