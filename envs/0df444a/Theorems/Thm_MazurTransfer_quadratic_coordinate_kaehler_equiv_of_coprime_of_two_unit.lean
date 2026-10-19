-- Prove2me | Theorems.Thm_MazurTransfer_quadratic_coordinate_kaehler_equiv_of_coprime_of_two_unit
-- name    : MazurTransfer.quadratic_coordinate_kaehler_equiv_of_coprime_of_two_unit
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T04:58:14.703931+00:00
-- url     : https://prove2.me/theorems/fb99428c-bc17-466d-842e-ba693db90772
-- title:
--   Coprime quadratic curve coordinates have a free rank-one differential module
-- statement:
--   Let $R$ be a commutative ring, let $f\in R[X]$ be coprime to its derivative, and assume that two is a unit in $R$. Put $A=R[X,Y]/(Y^2-f(X))$, with the specified monic-quadratic presentation. Then $$\Omega_{A/R}\cong A$$ as $A$-modules. This supplies the differential calculation for both actual affine charts of the order-thirteen integral curve, before applying the relative-dimension-one criterion.
-- source:
--   New direct specialization of the public Proved mixed_quadratic_coordinate_kaehler_equiv theorem to zero mixed term. An explicit Jacobian unit identity is built from the polynomial Bezout identity and the inverse of two, then the quadratic polynomial presentations are identified by an explicit equality. The solution passes native, strict and complete frontend checks; its exact public type is compared by a closed checked theorem and kernel equality. The first failed normalization attempt has no mathematical credit. Design boundary and named actual relative-dimension downstream consumer are retained in the Apache-2.0 source. Vas and contributors.

import Mathlib
open Polynomial
universe u

theorem MazurTransfer.quadratic_coordinate_kaehler_equiv_of_coprime_of_two_unit (R : Type u) [CommRing R] (f : Polynomial R)
    (hf : IsCoprime f f.derivative) (h2 : IsUnit (2 : R)) :
    Nonempty (Ω[AdjoinRoot ((X ^ 2 - C f) : Polynomial (Polynomial R))⁄R] ≃ₗ[AdjoinRoot ((X ^ 2 - C f) : Polynomial (Polynomial R))]
      AdjoinRoot ((X ^ 2 - C f) : Polynomial (Polynomial R)))  := by sorry
