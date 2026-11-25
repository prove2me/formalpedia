-- Prove2me | Theorems.Thm_GlobalTheory_grpObj_of_dense_fibres
-- name    : GlobalTheory.grpObj_of_dense_fibres
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:50:35.530957+00:00
-- url     : https://prove2.me/theorems/5eeded62-c783-4602-ae45-2bacd3ea6121
-- title:
--   Global Theory: grp Obj of dense fibres
-- statement:
--   The Global Theory construction uses the grp Obj of dense fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GrpObjOfDenseFibres.lean#L72-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GrpObjOfDenseFibres.lean#L72-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjOfDenseFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GrpDense FibreGrp

theorem GlobalTheory.grpObj_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsReduced R] (Z : Over (Sp R)) (m : Z ⊗ Z ⟶ Z) (i : Z ⟶ Z) (e : 𝟙_ (Over (Sp R)) ⟶ Z) (Sg : Set (Sp R)), Dense Sg → Smooth Z.hom → IsProper Z.hom → GeometricallyConnected Z.hom → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (A : Over (Sp K)) (_ : GrpObj A) (φ : A.left ⟶ Z.left), p ∈ Set.range x ∧ IsCommMonObj A ∧ IsPullback φ A.hom Z.hom x ∧ (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) ∧ φ ≫ i.left = (ι[A]).left ≫ φ ∧ x ≫ e.left = (η[A]).left ≫ φ) → ∃ _ : GrpObj Z, μ[Z] = m ∧ η[Z] = e ∧ ι[Z] = i ∧ IsAbelianScheme Z ∧ ∀ (S' : Scheme.{0}) (x : S' ⟶ Sp R) (A : Over S') [GrpObj A] (φ : A.left ⟶ Z.left), IsPullback φ A.hom Z.hom x → (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) → IsGrpPullback A Z x φ := by sorry
