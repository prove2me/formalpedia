-- Prove2me | Theorems.Thm_GlobalTheory_SheafPull_comp_extMap_right
-- name    : GlobalTheory.SheafPull.comp_extMap_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:13:02.50359+00:00
-- url     : https://prove2.me/theorems/cf775ac0-2f5e-4906-bc9c-2933a9dd6330
-- title:
--   Sheaf Pull: comp ext Map right
-- statement:
--   The Sheaf Pull construction uses the comp ext Map right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L42-L46

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
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasExt.{w} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasExt.{w'} B]
  (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

theorem GlobalTheory.SheafPull.comp_extMap_right {Z F : A} {Z' G G' : B} (a : Z' ⟶ Φ.obj Z) (b : Φ.obj F ⟶ G)
    (t : G ⟶ G') (n : ℕ) (x : Ext.{w} Z F n) :
    (extMap.{w, w'} Φ a b n x).comp (Ext.mk₀ t) (add_zero n) =
      extMap.{w, w'} Φ a (b ≫ t) n x := by sorry
