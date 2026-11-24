-- Prove2me | Theorems.Thm_GlobalTheory_SheafPull_comp_extMap_left
-- name    : GlobalTheory.SheafPull.comp_extMap_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:12:37.080948+00:00
-- url     : https://prove2.me/theorems/af524dfe-a446-409a-9117-381d0fda4d4b
-- title:
--   Sheaf Pull: comp ext Map left
-- statement:
--   The Sheaf Pull construction uses the comp ext Map left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L55-L59

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

theorem GlobalTheory.SheafPull.comp_extMap_left {Z F : A} {Z' Z₁ G : B} (a : Z' ⟶ Φ.obj Z) (b : Φ.obj F ⟶ G)
    (t : Z₁ ⟶ Z') (n : ℕ) (x : Ext.{w} Z F n) :
    (Ext.mk₀ t).comp (extMap.{w, w'} Φ a b n x) (zero_add n) =
      extMap.{w, w'} Φ (t ≫ a) b n x := by sorry
