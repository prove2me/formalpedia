-- Prove2me | Theorems.Thm_GlobalTheory_SheafPull_freeToPullback_comp_map
-- name    : GlobalTheory.SheafPull.freeToPullback_comp_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:47.047545+00:00
-- url     : https://prove2.me/theorems/af5126fc-dd84-4ed1-9d98-764cd7f56259
-- title:
--   Sheaf Pull: free To Pullback comp map
-- statement:
--   The Sheaf Pull construction uses the free To Pullback comp map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L132-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L132-L159

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

theorem GlobalTheory.SheafPull.freeToPullback_comp_map {V V' : C} {W : D} (i : W ⟶ p.obj V') (k : V' ⟶ V) :
    freeToPullback J K p i ≫ (p.sheafPullback AddCommGrpCat.{v} J K).map ((freeYoneda J).map k) =
      freeToPullback J K p (i ≫ p.map k) := by sorry
