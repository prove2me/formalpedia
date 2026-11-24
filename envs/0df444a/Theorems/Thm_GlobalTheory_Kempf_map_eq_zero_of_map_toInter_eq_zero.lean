-- Prove2me | Theorems.Thm_GlobalTheory_Kempf_map_eq_zero_of_map_toInter_eq_zero
-- name    : GlobalTheory.Kempf.map_eq_zero_of_map_toInter_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:48:09.90783+00:00
-- url     : https://prove2.me/theorems/07ae96da-e059-4fa6-9616-a6edaf42b3aa
-- title:
--   Kempf: map eq zero of map to Inter eq zero
-- statement:
--   The Kempf construction uses the map eq zero of map to Inter eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L225-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L225-L231

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
variable {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
open SheafLES

theorem GlobalTheory.Kempf.map_eq_zero_of_map_toInter_eq_zero {W : Opens X} {F G : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ G) [IsIso ((toInter AddCommGrpCat.{u} W).app G)] {n : ℕ} {V : Opens X}
    {α : Sheaf.H'.{w} F n V} (h : map.{w} ((toInter AddCommGrpCat.{u} W).app F) n V α = 0) :
    map.{w} f n V α = 0 := by sorry
