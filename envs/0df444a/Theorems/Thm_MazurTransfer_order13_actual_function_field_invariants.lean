-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_function_field_invariants
-- name    : MazurTransfer.order13_actual_function_field_invariants
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T22:08:13.945405+00:00
-- url     : https://prove2.me/theorems/c61b255f-3e92-4b5f-9f3d-d0f0e1e8715a
-- title:
--   Literal order-13 function field: constant field, genus two, and an actual affine cover
-- statement:
--   Let $C/K$ be the literal order-13 curve over a perfect field $K$ with $104\ne0$. Equip its actual scheme-theoretic function field $K(C)$ with the algebra structure induced by the actual map $C\to\operatorname{Spec}K$. It is a finite-type curve function field with full constant field $K$ and
--   \[
--   g\bigl(K(C)/K\bigr)=2.
--   \]
--   An actual two-affine-open cover of $C$ is also constructed. Neither a supplied function-field model nor supplied curve, constant-field, genus, or cover hypotheses are imposed. These invariants connect the arithmetic divisor class group of the literal function field to the represented Picard scheme, and support the finite-field point-count comparison.
-- source:
--   Vas and contributors, MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0, https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Full valuation, Cech and function-field genus infrastructure reused from official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Complete actual curve/function-field comparison proofs from our audited good-characteristic Picard cache; no abstract replacement curve is introduced.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
open AlgebraicGeometry AlgebraicCurve CategoryTheory

theorem MazurTransfer.order13_actual_function_field_invariants.{u}
    (K : Type u) [Field K] [PerfectField K] (h104 : (104 : K) ≠ 0) :
    letI : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K) :=
      (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K h104).1
    letI : Algebra K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField :=
      (baseToFunctionField (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)).toAlgebra
    IsCurveOver K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField ∧
      Algebra.EssFiniteType K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField ∧
      ConstantsAreBase K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField ∧
      genusFF K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField = 2 ∧
      Nonempty (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).TwoAffineOpenCover := by sorry
