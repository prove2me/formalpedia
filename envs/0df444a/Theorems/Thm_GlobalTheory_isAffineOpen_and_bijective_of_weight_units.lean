-- Prove2me | Theorems.Thm_GlobalTheory_isAffineOpen_and_bijective_of_weight_units
-- name    : GlobalTheory.isAffineOpen_and_bijective_of_weight_units
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:25:03.838155+00:00
-- url     : https://prove2.me/theorems/7ae3c9b0-701d-4e7e-b789-64b52b416712
-- title:
--   Global Theory: is Affine Open and bijective of weight units
-- statement:
--   The Global Theory construction uses the is Affine Open and bijective of weight units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenAndBijectiveOfWeightUnits.lean#L154-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenAndBijectiveOfWeightUnits.lean#L154-L231

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
open TorusTrivial

theorem GlobalTheory.isAffineOpen_and_bijective_of_weight_units :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G B : Over S) [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → ∀ (V : B.left.Opens), IsAffineOpen V → ∀ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, (∀ (χ : X) (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)), (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom (u (Multiplicative.ofAdd χ)).val = t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom (u (Multiplicative.ofAdd χ)).val) → IsAffineOpen (q.left ⁻¹ᵁ V) ∧ Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom ((Units.coeHom _).comp u) (fun _ _ => Commute.all _ _)) := by sorry
