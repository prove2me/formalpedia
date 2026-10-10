-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_integral_curve_flat_finitely_presented_and_smooth
-- name    : MazurTransfer.order13_actual_integral_curve_flat_finitely_presented_and_smooth
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T01:15:01.772166+00:00
-- url     : https://prove2.me/theorems/7db2411f-98a6-4ed6-b65d-18f66e65eb88
-- title:
--   Flat integral order-13 curve, smooth after inverting 104
-- statement:
--   Let $R$ be any commutative ring, and let $X_R\to\operatorname{Spec}R$ be the literal two-chart curve obtained by gluing the affine equation
--
--   $$y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$$
--
--   to its reciprocal chart using $x=z^{-1}$ and $y=wz^{-3}$. The structural morphism is flat and locally of finite presentation. If $104$ is a unit in $R$, the same actual morphism is smooth.
--
--   This constructs smooth integral curve families over bases where $104$ is invertible, including the bases needed at the primes $3$ and $5$. It supplies the flatness and smoothness part of a good-reduction construction. Properness, identification of fibres, a compatible Picard family and rational rank zero are separate assertions.
-- source:
--   MazurTheorem WIP, pin 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned extension of the checked quadratic-coordinate and smoothness proofs to arbitrary commutative rings; no new upstream source is imported.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve

open CategoryTheory AlgebraicGeometry

theorem MazurTransfer.order13_actual_integral_curve_flat_finitely_presented_and_smooth.{u}
    (R : Type u) [CommRing R] :
    Flat (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase R) ∧
    LocallyOfFinitePresentation (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase R) ∧
    (IsUnit (104 : R) →
      Smooth (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase R)) := by sorry
