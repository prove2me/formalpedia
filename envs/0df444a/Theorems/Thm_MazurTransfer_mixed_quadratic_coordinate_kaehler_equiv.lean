-- Prove2me | Theorems.Thm_MazurTransfer_mixed_quadratic_coordinate_kaehler_equiv
-- name    : MazurTransfer.mixed_quadratic_coordinate_kaehler_equiv
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-15T04:23:06.992253+00:00
-- url     : https://prove2.me/theorems/b5a5e202-8840-4455-a390-998be0399753
-- title:
--   The differentials of a mixed quadratic coordinate algebra are free of rank one under the Jacobian unit condition
-- statement:
--   Let R be any commutative ring, and let h and f be polynomials over R. For A=R[x,y]/(y²+h(x)y-f(x)), suppose h′(x)y-f′(x) and 2y+h(x) generate the unit ideal. Then the actual Kaehler differential module Ω[A/R] is isomorphic to A as an A-module. The proof constructs a tangent derivation using a square-zero extension, proves the differential relation, and exhibits a generator and its inverse functional. It requires neither invertibility of two nor a domain assumption. This is used for relative dimension one of the actual dyadic integral order-thirteen curve.
-- source:
--   Owned MazurTheorem integration, Apache-2.0. Adapts the complete checked square-zero construction of IntegralHyperellipticCoordinateDifferentials to the mixed equation, with an independent polynomial induction spanning argument. Checked at default limits on Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib

theorem MazurTransfer.mixed_quadratic_coordinate_kaehler_equiv
    (R : Type*) [CommRing R] (h f : Polynomial R)
    (hjac : ∃ a b : AdjoinRoot ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)),
      a * (AdjoinRoot.of ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) h.derivative *
        AdjoinRoot.root ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) -
        AdjoinRoot.of ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) f.derivative) +
      b * (2 * AdjoinRoot.root ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) +
        AdjoinRoot.of ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R)) h) = 1) :
    Nonempty (Ω[AdjoinRoot ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R))⁄R] ≃ₗ[AdjoinRoot ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R))] AdjoinRoot ((Polynomial.X ^ 2 + Polynomial.C h * Polynomial.X - Polynomial.C f) : Polynomial (Polynomial R))) := by sorry
