-- Prove2me | Theorems.Thm_MazurTransfer_FieldDivisorComparison_nonempty_iso_tensorUnit_of_principal_presentation
-- name    : MazurTransfer.FieldDivisorComparison.nonempty_iso_tensorUnit_of_principal_presentation
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T19:23:43.618758+00:00
-- url     : https://prove2.me/theorems/d5e9b26d-8208-422f-ab83-82517be5dbb3
-- title:
--   A principal full divisor presentation and numerical degree zero trivialize a line bundle over the original field
-- statement:
--   Let X be an integral smooth proper geometrically irreducible curve over an arbitrary field K. Let M be an invertible sheaf, with Euler characteristic equal to that of the structure sheaf on a chosen two-affine cover. If M has a full divisor presentation by a principal divisor E, then
--
--   $$M\simeq\mathcal O_X.$$
--
--   The statement retains the original naturality, scalar compatibility, injectivity and affine-open range conditions of the presentation. No perfection or algebraic-closure hypothesis is added. The result identifies the kernel of the geometric arithmetic Picard-class map.
-- source:
--   Complete original MazurTheorem LineBundlePrincipalPresentationTrivialityOverField.nonempty_iso_tensorUnit_of_principal_presentation. It uses the accepted arbitrary-field numerical line-bundle triviality theorem, the public places-of-cover theorem and the complete original global-section constructors from Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The affine-cover, section comparison and Cartier-divisor arguments reuse official
Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: a principal function-field presentation gives a nonzero global
section, and numerical degree zero then gives a trivial line bundle over the
actual base field. Named downstream consumer: the kernel of the order-13
arithmetic Picard-point map. No algebraic-closure hypothesis is imposed.
-/
import Definitions.Def_MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
import Definitions.Def_MazurTransfer_LineBundleGeometricDegreeZeroData
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_MazurTransfer_LineBundleFieldComparison_nonempty_iso_tensorUnit_of_curveEulerChar_eq_of_ne_zero
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open MazurTransfer.LineBundleFieldComparison

theorem MazurTransfer.FieldDivisorComparison.nonempty_iso_tensorUnit_of_principal_presentation
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (x : X ⟶ Spec (CommRingCat.of K))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIrreducible x]
    (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hχ : curveEulerChar x 𝒱 M = curveEulerChar x 𝒱 (𝟙_ X.Modules))
    (E : letI := (baseToFunctionField x).toAlgebra; Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hp : IsPresentation x M E φ)
    (hE : letI := (baseToFunctionField x).toAlgebra; Divisor.IsPrincipal E) :
    Nonempty (M ≅ 𝟙_ X.Modules) := by sorry
