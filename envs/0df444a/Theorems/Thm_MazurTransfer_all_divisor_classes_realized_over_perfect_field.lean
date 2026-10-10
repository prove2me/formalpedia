-- Prove2me | Theorems.Thm_MazurTransfer_all_divisor_classes_realized_over_perfect_field
-- name    : MazurTransfer.all_divisor_classes_realized_over_perfect_field
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T00:38:46.743338+00:00
-- url     : https://prove2.me/theorems/a5d073d9-607e-4fe1-b372-3922bb26fdae
-- title:
--   Every arithmetic divisor class has an invertible-sheaf realization over a perfect field
-- statement:
--   Let $X$ be a proper smooth integral curve over a perfect field $K$, with locally Noetherian underlying scheme and full constant field $K$ in its actual function field. For every arithmetic divisor $E$, there exist an invertible sheaf $M$, a divisor $G$, and injective rational-section maps on nonempty opens, natural under restriction and compatible with multiplication by regular functions. On every nonempty affine open, their images are exactly the local Riemann–Roch spaces of $G$, and
--
--   $$G-E\text{ is principal}.$$
--
--   Thus every arithmetic divisor class is realized by a genuine invertible sheaf and full section presentation. Arbitrary integer coefficients and nonrational closed points are included. The result supplies the divisor-realization step in surjectivity of the arithmetic Picard correspondence for the literal order-13 curve.
-- source:
--   Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Separately checked perfect-field adaptation and finite-support induction by Vas and contributors; downstream MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Original source attribution retained.

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicCurve

theorem MazurTransfer.all_divisor_classes_realized_over_perfect_field.{u}
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    (x : X ⟶ Spec (CommRingCat.of K)) [IsProper x] [SmoothOfRelativeDimension 1 x]
    (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.ConstantsAreBase K X.functionField)
    (E : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ (M : X.Modules), Scheme.Modules.IsInvertible M ∧
      ∃ (G : AlgebraicCurve.Divisor K X.functionField)
        (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u)),
        (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m) ∧
        (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
        (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
        (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) G : Set X.functionField)) ∧
        AlgebraicCurve.Divisor.IsPrincipal (G - E) := by sorry
