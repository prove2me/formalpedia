-- Prove2me | Theorems.Thm_GlobalTheory_TorusTrivial_isAffine_and_bijective
-- name    : GlobalTheory.TorusTrivial.isAffine_and_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:18.337398+00:00
-- url     : https://prove2.me/theorems/47f2c127-c388-4b78-a796-e131398e47f6
-- title:
--   Torus Trivial: is Affine and bijective
-- statement:
--   The Torus Trivial construction uses the is Affine and bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenAndBijectiveOfWeightUnits.lean#L56-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenAndBijectiveOfWeightUnits.lean#L56-L134

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
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
open GlobalTheory
open GlobalTheory.TorusTrivial

theorem GlobalTheory.TorusTrivial.isAffine_and_bijective {S : Scheme.{0}} {X : Type} [AddCommGroup X] {W V : Over S}
    [IsAffine V.left] (τ : W ⟶ splitTorus S X) (q : W ⟶ V) [IsIso (lift τ q)]
    {A : CommRingCat.{0}} (e : A ≅ Γ(V.left, ⊤)) (f : AddMonoidAlgebra A X →+* Γ(W.left, ⊤))
    (hf₁ : ∀ a : A, f (AddMonoidAlgebra.single 0 a) = q.left.appTop.hom (e.hom.hom a))
    (hf₂ : ∀ χ : X, f (AddMonoidAlgebra.single χ 1) = τ.left.appTop.hom (charUnit S X χ).val) :
    IsAffine W.left ∧ Function.Bijective f := by sorry
