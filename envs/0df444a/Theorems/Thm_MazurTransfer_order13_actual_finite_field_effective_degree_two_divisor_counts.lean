-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_finite_field_effective_degree_two_divisor_counts
-- name    : MazurTransfer.order13_actual_finite_field_effective_degree_two_divisor_counts
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T13:57:08.283696+00:00
-- url     : https://prove2.me/theorems/cb133864-bbbe-4b6e-9e6e-1e728850e435
-- title:
--   Actual order-13 curve: all effective degree-two divisors over F3 and F5
-- statement:
--   Let $C_q$ be the literal smooth proper two-chart curve over $\mathbb F_q$ given by $y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$ and its reciprocal chart. Let $\operatorname{Eff}^2(C_q)$ be the set of effective integral divisors of degree two on its function field, with closed-point degrees over $\mathbb F_q$. Then
--
--   $$\lvert\operatorname{Eff}^2(C_3)\rvert=22,\qquad\lvert\operatorname{Eff}^2(C_5)\rvert=24.$$
--
--   This counts all effective degree-two divisors, including repeated rational points and quadratic places. It provides the divisor enumeration needed for the geometric Picard cardinality calculation. Linear-equivalence fibres, Picard-group cardinality, rational Jacobian rank and rational-point exclusion over $\mathbb Q$ are separate obligations.
--
--   Formalization Note: the function-field algebra comes from the actual curve-to-base morphism. The proof imports the already proved good-characteristic geometry, rational-section counts and exhaustive geometric degree-two closed-point counts.
-- source:
--   Vas and contributors, MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion . Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . The literal curve and original finite-field certificates underlie the accepted point counts. Full original FLT place-existence, stalk-range and function-field curve APIs are reused. Base-compatible residue-field, exhaustive rational-point and effective-divisor enumeration bridges are new checked work. Apache-2.0 headers and attribution retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_MazurTransfer_Order13DegreeTwoClosedPoints
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
import Theorems.Thm_MazurTransfer_order13_actual_degree_two_closed_point_counts
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
open AlgebraicGeometry AlgebraicCurve CategoryTheory
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 3)) :=
  (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 (ZMod 3) (by decide)).1
noncomputable local instance : Algebra (ZMod 3) (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 3)).functionField :=
  (AlgebraicCurve.baseToFunctionField (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod 3))).toAlgebra
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 5)) :=
  (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 (ZMod 5) (by decide)).1
noncomputable local instance : Algebra (ZMod 5) (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 5)).functionField :=
  (AlgebraicCurve.baseToFunctionField (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod 5))).toAlgebra

theorem MazurTransfer.order13_actual_finite_field_effective_degree_two_divisor_counts :
    Nat.card {D : AlgebraicCurve.Divisor (ZMod 3)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 3)).functionField //
      (∀ v, 0 ≤ D v) ∧ AlgebraicCurve.Divisor.degree D = 2} = 22 ∧
    Nat.card {D : AlgebraicCurve.Divisor (ZMod 5)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 5)).functionField //
      (∀ v, 0 ≤ D v) ∧ AlgebraicCurve.Divisor.degree D = 2} = 24 := by sorry
