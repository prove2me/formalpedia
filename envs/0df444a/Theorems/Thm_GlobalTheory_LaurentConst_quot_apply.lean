-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_quot_apply
-- name    : GlobalTheory.LaurentConst.quot_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:04.612657+00:00
-- url     : https://prove2.me/theorems/da8b87db-375e-4158-a239-5a474969068d
-- title:
--   Laurent Const: quot apply
-- statement:
--   The Laurent Const construction uses the quot apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L235-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L235-L248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {W Z : Scheme.{0}}

theorem GlobalTheory.LaurentConst.quot_apply {D A : Type} [CommRing D] [CommRing A] (f : Spec (.of D) ⟶ B.left)
    (α β : D →+* A) (h) (H : ∀ (C : Type) [CommRing C] [IsReduced C] (ρ : A →+* C),
      ρ.comp α = ρ.comp β) (z : Spec (.of A)) :
    quot (Spec.map (CommRingCat.ofHom α) ≫ f) (Spec.map (CommRingCat.ofHom β) ≫ f) h z =
      ((Spec.map (CommRingCat.ofHom α) ≫ f) ≫ B.hom ≫ (η[B] : 𝟙_ (Over S) ⟶ B).left) z := by sorry
