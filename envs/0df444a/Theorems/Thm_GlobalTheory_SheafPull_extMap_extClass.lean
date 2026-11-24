-- Prove2me | Theorems.Thm_GlobalTheory_SheafPull_extMap_extClass
-- name    : GlobalTheory.SheafPull.extMap_extClass
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:12:41.63081+00:00
-- url     : https://prove2.me/theorems/3550f760-c45f-406a-b0de-991cba5a1e5d
-- title:
--   Sheaf Pull: ext Map ext Class
-- statement:
--   The Sheaf Pull construction uses the ext Map ext Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L70-L77

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

theorem GlobalTheory.SheafPull.extMap_extClass {Z : A} {Z' : B} (a : Z' ⟶ Φ.obj Z) {S : ShortComplex A}
    {T : ShortComplex B} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S.map Φ ⟶ T) (n : ℕ)
    (x : Ext.{w} Z S.X₃ n) :
    extMap.{w, w'} Φ a (F := S.X₁) φ.τ₁ (n + 1) (x.comp hS.extClass rfl) =
      (extMap.{w, w'} Φ a (F := S.X₃) φ.τ₃ n x).comp hT.extClass rfl := by sorry
