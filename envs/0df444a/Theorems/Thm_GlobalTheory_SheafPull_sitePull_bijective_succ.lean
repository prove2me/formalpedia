-- Prove2me | Theorems.Thm_GlobalTheory_SheafPull_sitePull_bijective_succ
-- name    : GlobalTheory.SheafPull.sitePull_bijective_succ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:43.5246+00:00
-- url     : https://prove2.me/theorems/ae516d04-e39a-4561-9f5f-1b23ee183135
-- title:
--   Sheaf Pull: site Pull bijective succ
-- statement:
--   The Sheaf Pull construction uses the site Pull bijective succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L236-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L236-L265

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

theorem GlobalTheory.SheafPull.sitePull_bijective_succ {S : ShortComplex (Sheaf J AddCommGrpCat.{v})}
    {T : ShortComplex (Sheaf K AddCommGrpCat.{v})} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T.map (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K)) (n : ℕ)
    {V : C} {W : D} (i : W ⟶ p.obj V)
    (h₂ : Function.Surjective (sitePull.{w, w'} p (G := T.X₂) φ.τ₂ n i))
    (h₃ : Function.Bijective (sitePull.{w, w'} p (G := T.X₃) φ.τ₃ n i))
    (hV : Subsingleton (Sheaf.H'.{w} S.X₂ (n + 1) V))
    (hW : Subsingleton (Sheaf.H'.{w'} T.X₂ (n + 1) W)) :
    Function.Bijective (sitePull.{w, w'} p (G := T.X₁) φ.τ₁ (n + 1) i) := by sorry
