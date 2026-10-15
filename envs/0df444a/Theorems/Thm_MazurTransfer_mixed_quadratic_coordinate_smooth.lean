-- Prove2me | Theorems.Thm_MazurTransfer_mixed_quadratic_coordinate_smooth
-- name    : MazurTransfer.mixed_quadratic_coordinate_smooth
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-15T00:09:44.464828+00:00
-- url     : https://prove2.me/theorems/3110cf46-fd3b-48e7-a5e1-891592128487
-- title:
--   A mixed quadratic coordinate algebra is smooth when its Jacobian generates the unit ideal
-- statement:
--   Let R be any commutative ring and let h and f be polynomials over R. In the coordinate algebra R[x,y]/(y²+h(x)y-f(x)), suppose the two Jacobian elements h′(x)y-f′(x) and 2y+h(x) generate the unit ideal. Then the coordinate algebra is smooth over R. The proof lifts arbitrary homomorphisms across every square-zero ideal by an explicit two-variable correction, and uses finite presentation. No invertibility of 2 or field assumption is required. This theorem is used for the mixed quadratic integral charts needed in the order-13 descent at 2.
-- source:
--   Owned MazurTheorem integration, Apache-2.0. MixedQuadraticCoordinateJacobian and MixedQuadraticCoordinateSmooth; self-contained proof checked at default limits on Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib

theorem MazurTransfer.mixed_quadratic_coordinate_smooth
    (R : Type*) [CommRing R] (h f : Polynomial R)
    (hjac : ∃ a b : AdjoinRoot ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)),
      a * (AdjoinRoot.of ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) h.derivative *
        AdjoinRoot.root ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) -
        AdjoinRoot.of ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) f.derivative) +
      b * (2 * AdjoinRoot.root ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) +
        AdjoinRoot.of ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) h) = 1) :
    Algebra.Smooth R (AdjoinRoot ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R))) := by sorry
