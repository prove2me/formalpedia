-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
-- name    : MazurTransfer.order13_actual_integral_curve_geometrically_integral
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T02:33:55.748767+00:00
-- url     : https://prove2.me/theorems/ba222ac6-3f83-4542-b909-9492ac02b513
-- title:
--   Actual integral curve is geometrically integral where 104 is invertible
-- statement:
--   For every commutative ring R in which 104 is a unit, the literal two-chart order-13 curve is geometrically integral over Spec R. Every pullback along a morphism from the spectrum of any field is an integral scheme. Whole-curve base-change isomorphisms and good-characteristic field integrality are constructed, accepted dependencies. No field, perfectness, supplied model, fibre-identification or geometric-integrality hypothesis on R is assumed. This supplies a geometric-integrality input for the actual integral Picard family over Z[1/104]. Relative dimension one, integral Picard representability, rational rank zero and compatible torsion specialization remain separate obligations.
-- source:
--   MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned whole-curve base-change and good-characteristic field geometry with Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
import Theorems.Thm_MazurTransfer_order13_actual_whole_curve_base_change_isomorphism

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve

theorem MazurTransfer.order13_actual_integral_curve_geometrically_integral.{u}
    (R : Type u) [CommRing R] (h104 : IsUnit (104 : R)) :
    GeometricallyIntegral (curveToBase R) := by sorry
