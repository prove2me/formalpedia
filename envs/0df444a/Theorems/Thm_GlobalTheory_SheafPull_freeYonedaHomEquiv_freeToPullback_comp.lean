-- Prove2me | Theorems.Thm_GlobalTheory_SheafPull_freeYonedaHomEquiv_freeToPullback_comp
-- name    : GlobalTheory.SheafPull.freeYonedaHomEquiv_freeToPullback_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:22.101676+00:00
-- url     : https://prove2.me/theorems/e2e295e8-d85b-4ac8-a59c-abd8b428a5dd
-- title:
--   Sheaf Pull: free Yoneda Hom Equiv free To Pullback comp
-- statement:
--   The Sheaf Pull construction uses the free Yoneda Hom Equiv free To Pullback comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L115-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L115-L123

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

theorem GlobalTheory.SheafPull.freeYonedaHomEquiv_freeToPullback_comp {V : C} {W : D} (i : W ⟶ p.obj V)
    {G : Sheaf K AddCommGrpCat.{v}}
    (b : (p.sheafPullback AddCommGrpCat.{v} J K).obj ((freeYoneda J).obj V) ⟶ G) :
    freeYonedaHomEquiv W G (freeToPullback J K p i ≫ b) =
      G.obj.map i.op (freeYonedaHomEquiv V _
        ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _ b)) := by sorry
