-- Prove2me | Theorems.Thm_GlobalTheory_SheafPull_equivZero_sitePull
-- name    : GlobalTheory.SheafPull.equivZero_sitePull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:58.105183+00:00
-- url     : https://prove2.me/theorems/0df49f11-3fa4-43b2-9207-a1fcb9fce029
-- title:
--   Sheaf Pull: equiv Zero site Pull
-- statement:
--   The Sheaf Pull construction uses the equiv Zero site Pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L170-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L170-L178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w w' w'' v u u₁ v₁ u₂ v₂
noncomputable section
open GlobalTheory
open GlobalTheory.SheafPull
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  (p : C ⥤ D) [p.IsContinuous J K]
  [(p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]
open SheafLES
variable [PreservesFiniteLimits (p.sheafPullback AddCommGrpCat.{v} J K)]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{v})]
  {F F' : Sheaf J AddCommGrpCat.{v}} {G G' : Sheaf K AddCommGrpCat.{v}}

theorem GlobalTheory.SheafPull.equivZero_sitePull (φ : F ⟶ (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj G)
    {V : C} {W : D} (i : W ⟶ p.obj V) (x : Sheaf.H'.{w} F 0 V) :
    equivZero G W (sitePull.{w, w'} p φ 0 i x) =
      G.obj.map i.op (φ.hom.app (op V) (equivZero F V x)) := by sorry
