-- Prove2me | Theorems.Thm_MazurTransfer_presentation_ratio_principal_over_perfect_field
-- name    : MazurTransfer.presentation_ratio_principal_over_perfect_field
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T22:57:38.679566+00:00
-- url     : https://prove2.me/theorems/9ee49c39-b4aa-46e3-9f23-b520afd67081
-- title:
--   Divisor presentations differ by a principal divisor over a perfect field
-- statement:
--   Let X be a proper smooth integral curve over a perfect field K whose literal function field has constant field K. Two compatible injective rational-section presentations of the same sheaf, with local images given by their actual divisor Riemann–Roch spaces and a nonzero section, differ by multiplication by a nonzero rational function g. Their coefficients differ by ord(g), so their divisor difference is principal. This applies over Q, F3, and F5 without assuming algebraic closure. It supplies the independence-of-presentation argument for the unchanged arithmetic Picard group correspondence; it does not prove rank zero or reduction bounds.
-- source:
--   Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Separately checked perfect-field adaptation by Vas and contributors, downstream MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0, https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c .

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace

theorem MazurTransfer.presentation_ratio_principal_over_perfect_field.{u}
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.ConstantsAreBase K X.functionField)
    (M : X.Modules)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField))
    (hsec : ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ g : X.functionField, g ≠ 0 ∧
      (∀ (U : X.Opens) [Nonempty U] (m : Γ(M, U)), φ' U m = g * φ U m) ∧
      (∀ v : AlgebraicCurve.Place K X.functionField, D v = D' v + v.ord g) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D - D') := by sorry
