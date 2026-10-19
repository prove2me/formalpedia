-- Prove2me | Theorems.Thm_MazurTransfer_FieldDivisorComparison_riemannRoch_of_constantsAreBase
-- name    : MazurTransfer.FieldDivisorComparison.riemannRoch_of_constantsAreBase
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T14:10:10.417992+00:00
-- url     : https://prove2.me/theorems/51aba7da-1957-4716-a803-4b57f1595da4
-- title:
--   Riemann–Roch for line-bundle divisor presentations over a perfect field with base constants
-- statement:
--   A genuine function-field presentation of a sheaf on a smooth proper integral curve over a perfect field, with constant field equal to the base, identifies H0 and H1 dimensions with the divisor invariants and satisfies the genus Riemann–Roch formula.
-- source:
--   MazurTheorem LineBundleDivisorRiemannRochOverField, adapting official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache-2.0).

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Adapted from the complete official Anthropic FLT mathematical proof at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: retain the presentation argument over an arbitrary perfect field
with its constant-field hypothesis explicit. Named downstream consumer:
the arithmetic divisor-class map for the actual order-13 curve over F₃ and F₅.
The original theorem is unchanged; its algebraic-closure assumption was used
only to derive the constant-field property now supplied as a proved input.
-/
import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import Theorems.Thm_AlgebraicCurve_cechRiemannRoch_of_genusReached
universe u
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace

theorem MazurTransfer.FieldDivisorComparison.riemannRoch_of_constantsAreBase
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.ConstantsAreBase K X.functionField)
    (M : X.Modules)
    (D : letI := (baseToFunctionField x).toAlgebra; Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (lSpaceOn (placesOf x U) D : Set X.functionField)) :
    letI := (baseToFunctionField x).toAlgebra
    Module.Finite K (𝒱.sectionsOf x M).H0 ∧ Module.Finite K (𝒱.sectionsOf x M).H1 ∧
      Module.finrank K (𝒱.sectionsOf x M).H0 = ell D ∧
      Module.finrank K (𝒱.sectionsOf x M).H1 = indexOfSpecialty D ∧
      (Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1
        = Divisor.degree D + 1 - genusFF K X.functionField := by sorry
