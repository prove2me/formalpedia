-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_epi_and_isMonHom_iff
-- name    : GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:43.720618+00:00
-- url     : https://prove2.me/theorems/14c708a4-9c0a-4106-9e4e-81cb6222b966
-- title:
--   Field Base Change: epi and is Mon Hom iff
-- statement:
--   The Field Base Change construction uses the epi and is Mon Hom iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsMonHomIffOfIsGrpPullback.lean#L79-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsMonHomIffOfIsGrpPullback.lean#L79-L88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.FieldBaseChange

theorem GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K), (∀ (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), IsPullback φ p p₀ (spMap i) → Epi φ ∧ Flat φ ∧ Surjective φ ∧ IsAffineHom φ ∧ ∀ U : X₀.Opens, Function.Injective (φ.app U).hom) ∧ ∀ (A₀ B₀ : Over (Sp K₀)) (A B : Over (Sp K)) [GrpObj A₀] [GrpObj B₀] [GrpObj A] [GrpObj B] (φ : A.left ⟶ A₀.left) (ψ : B.left ⟶ B₀.left) (f₀ : A₀ ⟶ B₀) (f : A ⟶ B), IsGrpPullback A A₀ (spMap i) φ → IsGrpPullback B B₀ (spMap i) ψ → φ ≫ f₀.left = f.left ≫ ψ → (IsMonHom f ↔ IsMonHom f₀) := by sorry
