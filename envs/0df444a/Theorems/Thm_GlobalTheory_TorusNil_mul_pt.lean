-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_mul_pt
-- name    : GlobalTheory.TorusNil.mul_pt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:10:11.451593+00:00
-- url     : https://prove2.me/theorems/465a9d05-030d-43ec-9b29-140905b6aa3a
-- title:
--   Torus Nil: mul pt
-- statement:
--   The Torus Nil construction uses the mul pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L155-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L155-L211

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
variable {B : Over (Spec (CommRingCat.of A))} [GrpObj B] {R : Type} [CommRing R] [Algebra A R]
  (j : sp A R ⟶ B) [IsOpenImmersion j.left] (ε : R →ₐ[A] A) (hε : spm ε ≫ j = 1)
include hε

theorem GlobalTheory.TorusNil.mul_pt {C : Type} [CommRing C] [Algebra A C] (K : Ideal C) (hK : ∀ x ∈ K, IsNilpotent x)
    (φ₁ φ₂ φ : R →ₐ[A] C) (h₁ : ∀ a, φ₁ a - algebraMap A C (ε a) ∈ K)
    (h₂ : ∀ a, φ₂ a - algebraMap A C (ε a) ∈ K)
    (h : (spm φ₁ ≫ j) * (spm φ₂ ≫ j) = spm φ ≫ j) (a : R) :
    φ a - (φ₁ a + φ₂ a - algebraMap A C (ε a)) ∈ K ^ 2 := by sorry
