-- Prove2me | Theorems.Thm_MazurTransfer_closed_point_kernel_presentations_signed_divisor_classes
-- name    : MazurTransfer.closed_point_kernel_presentations_signed_divisor_classes
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T00:32:05.289392+00:00
-- url     : https://prove2.me/theorems/e5c0a072-ab34-4211-ac34-8cadbe981b41
-- title:
--   Closed-point kernel presentations represent both signed divisor classes
-- statement:
--   Let $X$ be a proper smooth integral curve over a perfect field $K$, with locally Noetherian underlying scheme and full constant field $K$ in its actual function field. Let $P:\operatorname{Spec}L\hookrightarrow X$ be an arbitrary closed field-valued point, let $v$ be the place whose valuation ring is the stalk at $P$, and let $n\geq0$. Write $I=\ker P$. Suppose $D,D′$ are divisors supplied by actual rational-section presentations of $(I^n)^{-1}$ and $I^n$. Each presentation is natural on nonempty restrictions, compatible with multiplication by regular functions, injective on nonempty opens, and has image equal to the corresponding local divisor Riemann–Roch space on every nonempty affine open. Then
--
--   $$D-n[v]\text{ and }D′+n[v]\text{ are principal}.$$
--
--   Thus the inverse ideal and ideal powers represent the positive and negative multiples of the closed-point class. The residue field $L$ is not required to equal $K$. This comparison supports realization of all arithmetic divisor classes and surjectivity of the Picard correspondence for the literal order-13 curve.
-- source:
--   Official Anthropic FLT, pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Complete separately checked perfect-field and arbitrary-residue-field adaptation by Vas and contributors. Downstream MazurTheorem WIP, pin 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Attribution retained; actual presentations and divisor quotient are used throughout.

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
open CategoryTheory AlgebraicGeometry AlgebraicCurve Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules CategoryTheory.MonoidalCategory

theorem MazurTransfer.closed_point_kernel_presentations_signed_divisor_classes.{u}
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsLocallyNoetherian X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra; ConstantsAreBase K X.functionField)
    {L : Type u} [Field L] (P : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion P] (n : ℕ)
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K X.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk (P.base (IsLocalRing.closedPoint L))) X.functionField).range =
        v.toValuationSubring.toSubring)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ((P.ker ^ n).invModule, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).invModule, U), φ V (((P.ker ^ n).invModule).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).invModule, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (φ' : ∀ U : X.Opens, Γ((P.ker ^ n).module, U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).module, U), φ' V (((P.ker ^ n).module).presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).module, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D - n • Finsupp.single v 1) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D' + n • Finsupp.single v 1) := by sorry
