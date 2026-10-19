-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_integral_chart_polynomials_coprime
-- name    : MazurTransfer.order13_actual_integral_chart_polynomials_coprime
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T05:00:45.925049+00:00
-- url     : https://prove2.me/theorems/d206b31b-c3f7-480d-b31e-2eb8521b8d68
-- title:
--   Both actual order-thirteen chart polynomials are coprime to their derivatives
-- statement:
--   Let $R$ be a commutative ring in which $104$ is a unit. Let $f$ be the literal sextic polynomial defining the ordinary order-thirteen chart and let $f^{\mathrm{rev}}$ be its specified reciprocal-chart polynomial. Then
--   $$\gcd(f,f')=1,\qquad\gcd(f^{\mathrm{rev}},(f^{\mathrm{rev}})')=1,$$
--   in the sense that each pair generates the unit ideal. These inputs provide the free rank-one differential modules needed for the actual integral relative-dimension-one proof.
-- source:
--   The two complete unchanged Bezout proofs from checked MazurTheorem Order13IntegralCurveSmooth.lean, packaged as their conjunction. Complete Lean frontend ranges retain both original helper declarations and their scope, with direct public literal-curve imports. Both original helper types are checked by closed kernel witnesses and the conjunction is checked against the public formal type. Original file header, source pin, Apache-2.0 and actual curve downstream consumers are retained. Vas and contributors.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
universe u

theorem MazurTransfer.order13_actual_integral_chart_polynomials_coprime (R : Type u) [CommRing R] (h104 : IsUnit (104 : R)) :
    IsCoprime (sexticPolynomial R) (sexticPolynomial R).derivative ∧
      IsCoprime (reciprocalPolynomial R) (reciprocalPolynomial R).derivative  := by sorry
