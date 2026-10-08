-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_affine_scheme_smooth
-- name    : MazurTransfer.order13_actual_affine_scheme_smooth
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T20:39:14.960183+00:00
-- url     : https://prove2.me/theorems/c724227d-52a3-4417-b757-ef49282de113
-- title:
--   Smoothness of the actual affine order-13 sextic over a characteristic-zero field
-- statement:
--   For every field $K$ of characteristic zero, let
--   \[f(x)=x^6+2x^5+x^4+2x^3+6x^2+4x+1.\]
--   The structure morphism
--   \[\operatorname{Spec}\bigl(K[x,y]/(y^2-f(x))\bigr)\longrightarrow\operatorname{Spec}K\]
--   is smooth. This is the actual affine order-13 coordinate algebra, spelled explicitly as a quadratic AdjoinRoot algebra in the formal statement. The closed proof artifact also verifies smoothness of the reciprocal chart and the original two-chart glued structure morphism. This result supplies geometric smoothness only: no genus, properness, Jacobian identification, or rational-point classification is assumed.
-- source:
--   Original affine and two-chart model by Vasily Ilin, retained whole with Apache-2.0 attribution: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry . New smoothness proof by Vas and contributors. The separability certificate is an explicit polynomial Bezout identity with constant 104; chart smoothness uses the separately proved MazurTransfer.hyperelliptic_coordinate_smooth theorem. Named downstream consumer: MazurTorsion.XOneThirteenProjectiveCurve.curveToBase_smooth. Design boundary: the actual morphism, with no arithmetic or Jacobian hypotheses.

import Mathlib

theorem MazurTransfer.order13_actual_affine_scheme_smooth (K : Type*) [Field K] [CharZero K] :
    _root_.AlgebraicGeometry.Smooth
      (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap K (AdjoinRoot
        ((Polynomial.X ^ 2 - Polynomial.C
          ((Polynomial.X : Polynomial K) ^ 6 + 2 * Polynomial.X ^ 5 +
            Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 + 6 * Polynomial.X ^ 2 +
            4 * Polynomial.X + 1)) : Polynomial (Polynomial K)))))) := by sorry
