-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_affine_scheme_integral
-- name    : MazurTransfer.order13_actual_affine_scheme_integral
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T19:47:24.357991+00:00
-- url     : https://prove2.me/theorems/4c598065-de4b-4d78-ba15-e5fa20d5d97e
-- title:
--   Integrality of the actual affine order-13 sextic in characteristic zero
-- statement:
--   Let $K$ be any field of characteristic zero, and put $f(x)=x^6+2x^5+x^4+2x^3+6x^2+4x+1$. The actual affine scheme
--   \[\operatorname{Spec}\bigl(K[x,y]/(y^2-f(x))\bigr)\]
--   is integral: its coordinate ring has no zero divisors and its spectrum is reduced and irreducible. The Lean statement spells this quotient as the quadratic AdjoinRoot algebra over $K[x]$.
--
--   This supplies the integrality prerequisite for the geometric and Picard/Jacobian treatment of the explicit order-13 curve. It assumes no rational-point classification, rank-zero calculation, or Jacobian representation.
-- source:
--   https://github.com/Vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry/XOneThirteenAffineCurve.lean ; original affine model by Vasily Ilin, preserved whole, Apache-2.0. New closed characteristic-zero irreducibility and integrality proof by Vas and contributors. Named checked downstream consumer: MazurTorsion.XOneThirteenAffineCurve.affineScheme_isIntegral. Design boundary: the actual affine spectrum, with no smoothness, genus, or Jacobian hypothesis.

import Mathlib

theorem MazurTransfer.order13_actual_affine_scheme_integral (K : Type*)
    [Field K] [CharZero K] :
    _root_.AlgebraicGeometry.IsIntegral
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of (AdjoinRoot
        ((Polynomial.X ^ 2 - Polynomial.C
          ((Polynomial.X : Polynomial K) ^ 6 + 2 * Polynomial.X ^ 5 +
            Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 + 6 * Polynomial.X ^ 2 +
            4 * Polynomial.X + 1)) : Polynomial (Polynomial K))))) := by sorry
