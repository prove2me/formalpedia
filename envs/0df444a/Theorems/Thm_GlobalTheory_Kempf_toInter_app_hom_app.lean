-- Prove2me | Theorems.Thm_GlobalTheory_Kempf_toInter_app_hom_app
-- name    : GlobalTheory.Kempf.toInter_app_hom_app
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:30.581554+00:00
-- url     : https://prove2.me/theorems/55a02fbe-73e2-4474-b12c-480c7a6c17dd
-- title:
--   Kempf: to Inter app hom app
-- statement:
--   The Kempf construction uses the to Inter app hom app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L62-L63

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

theorem GlobalTheory.Kempf.toInter_app_hom_app (W : Opens X) (F : X.Sheaf A) (B : Opens X) :
    ((toInter A W).app F).hom.app (op B) = F.obj.map (homOfLE inf_le_left).op := by sorry

attribute [defeq] GlobalTheory.Kempf.toInter_app_hom_app
