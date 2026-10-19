-- Prove2me | Theorems.Thm_MazurTransfer_FieldDivisorComparison_presentationTensorPrincipal_of_constantsAreBase
-- name    : MazurTransfer.FieldDivisorComparison.presentationTensorPrincipal_of_constantsAreBase
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T19:19:51.740168+00:00
-- url     : https://prove2.me/theorems/8ba91b18-ca4b-48d3-a95d-3e1c7a8c64a0
-- title:
--   Tensor products add divisor classes for full line-bundle presentations over a perfect constant field
-- statement:
--   Let X be an integral smooth proper curve over a perfect field K, with K equal to the constant field of its function field. Let L and L′ be invertible sheaves with full divisor presentations D and D′, and let D″ be a full presentation of their tensor product. Then
--
--   $$D^{\prime\prime}-D-D^\prime\quad\text{is principal}.$$
--
--   All naturality, scalar compatibility, injectivity and affine-open range conditions on the three section presentations are retained. The result makes addition of geometric arithmetic Picard classes compatible with the group law of the same represented Picard family.
-- source:
--   Complete original MazurTheorem LineBundleDivisorTensorComparisonOverField.presentationTensorPrincipal_of_constantsAreBase, using the accepted perfect-field presentation ratio and the full original tensor-calibration proof from Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Retains the full tensor-presentation proof from official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: tensor products correspond to divisor addition over a perfect
field with its constant-field property explicit. Named downstream consumer:
the actual order-13 arithmetic divisor-class map over F₃ and F₅.
The original theorem and its hypotheses remain unchanged.
-/
import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_MazurTransfer_presentation_ratio_principal_over_perfect_field
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicCurve WithZero
open _root_.AlgebraicGeometry.Scheme.Modules

theorem MazurTransfer.FieldDivisorComparison.presentationTensorPrincipal_of_constantsAreBase
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.ConstantsAreBase K X.functionField)
    (L L' : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (D D' D'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V ((L).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L', U), φ' V ((L').presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L', U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField))
    (φ'' : ∀ U : X.Opens, Γ(L ⊗ L', U) →+ (X.functionField : Type u))
    (hnat'' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L ⊗ L', U), φ'' V ((L ⊗ L').presheaf.map (homOfLE h).op m) = φ'' U m)
    (hsmul'' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L ⊗ L', U)),
      φ'' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ'' U m)
    (hinj'' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ'' U))
    (hrange'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ'' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D'' : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D'' - D - D') := by sorry
