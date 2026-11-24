-- Prove2me | Theorems.Thm_GlobalTheory_SheafPull_extMap_comp_right
-- name    : GlobalTheory.SheafPull.extMap_comp_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:33.268105+00:00
-- url     : https://prove2.me/theorems/c4ed03d4-0581-4a35-a197-aea4aacfffa5
-- title:
--   Sheaf Pull: ext Map comp right
-- statement:
--   The Sheaf Pull construction uses the ext Map comp right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L35-L40

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

theorem GlobalTheory.SheafPull.extMap_comp_right {Z F F' : A} {Z' G : B} (a : Z' ⟶ Φ.obj Z) (b : Φ.obj F' ⟶ G)
    (s : F ⟶ F') (n : ℕ) (x : Ext.{w} Z F n) :
    extMap.{w, w'} Φ a b n (x.comp (Ext.mk₀ s) (add_zero n)) =
      extMap.{w, w'} Φ a (Φ.map s ≫ b) n x := by sorry
