-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_finite_field_picard_cardinality
-- name    : MazurTransfer.order13_actual_finite_field_picard_cardinality
-- status  : Open
-- author  : @Vas
-- created : 2026-10-09T14:33:33.846287+00:00
-- url     : https://prove2.me/theorems/7a665ae8-8d06-4ab5-b637-564aca6f44c1
-- title:
--   Actual order-13 curve: degree-zero Picard groups over F3 and F5 have order 19
-- statement:
--   Let $C_q$ be the literal smooth proper two-chart curve over $\mathbb F_q$ given by $y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$ and its reciprocal chart. Write $\operatorname{Pic}^0(C_q)$ for the group of degree-zero function-field divisors modulo principal divisors, using closed-point degrees over the base field. Then
--
--   $$\lvert\operatorname{Pic}^0(C_3)\rvert=\lvert\operatorname{Pic}^0(C_5)\rvert=19.$$
--
--   These are the genuine divisor-class quotients of the literal curves. This finite-field arithmetic input supports the later reduction argument. Identification with rational points of a represented Jacobian, rational Jacobian rank over $\mathbb Q$, and the order-13 rational-point exclusion are separate obligations.
--
--   Formalization Note: integrality is derived from the already proved good-characteristic geometry, and the function-field base algebra is induced by the actual structure morphism. No supplied genus or Picard-order assumption is used.
-- source:
--   Vas and contributors, MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion . Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . The literal curve and original finite-field certificates underlie the accepted point counts. Full original FLT place-existence, stalk-range and function-field curve APIs are reused. Base-compatible residue-field, exhaustive rational-point and effective-divisor enumeration bridges are new checked work. Apache-2.0 headers and attribution retained. The new proof derives the unique canonical degree-two class through the original exists_weilCanonical_riemannRoch and counts its complete effective fibre through card_effective_sub_isPrincipal_of_finite. Degree-two class representatives and the genuine Pic0 surjection are newly checked bridges.

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

theorem MazurTransfer.order13_actual_finite_field_picard_cardinality :
    Nat.card (AlgebraicCurve.Pic0 (ZMod 3)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 3)).functionField) = 19 ∧
    Nat.card (AlgebraicCurve.Pic0 (ZMod 5)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 5)).functionField) = 19 := by sorry
