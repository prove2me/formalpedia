-- Prove2me | Theorems.Thm_GlobalTheory_Kempf_toInter_app_comp_map_comp_inv
-- name    : GlobalTheory.Kempf.toInter_app_comp_map_comp_inv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:47:48.555592+00:00
-- url     : https://prove2.me/theorems/808cd0f0-cfd8-407f-9f47-b2be241278cf
-- title:
--   Kempf: to Inter app comp map comp inv
-- statement:
--   The Kempf construction uses the to Inter app comp map comp inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L91-L95

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

theorem GlobalTheory.Kempf.toInter_app_comp_map_comp_inv (W : Opens X) {F G : X.Sheaf A} (f : F ⟶ G)
    [IsIso ((toInter A W).app G)] :
    (toInter A W).app F ≫ (interSheaf A W).map f ≫ inv ((toInter A W).app G) = f := by sorry
