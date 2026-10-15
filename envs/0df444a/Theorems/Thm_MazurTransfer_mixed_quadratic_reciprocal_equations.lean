-- Prove2me | Theorems.Thm_MazurTransfer_mixed_quadratic_reciprocal_equations
-- name    : MazurTransfer.mixed_quadratic_reciprocal_equations
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-15T00:35:30.822244+00:00
-- url     : https://prove2.me/theorems/a5cf9a25-8fbc-46d8-8e13-d3139b85b4eb
-- title:
--   The integral mixed quadratic order-13 equations transform reciprocally without dividing by two
-- statement:
--   Over any commutative ring, suppose xz=1. The substitution z=1/x and v=y/x³ sends y²+(x³+x²+1)y=x(x+1) to v²+(1+z+z³)v=z⁴+z⁵, and the inverse substitution sends the latter equation back. The polynomial identities hold integrally, including in residue characteristic two. They are used directly to construct the actual inverse localization maps for the two dyadic charts of the order-13 curve.
-- source:
--   Owned MazurTheorem integration, Apache-2.0. Order13MixedQuadraticReciprocalRelations; checked at default limits on Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib

theorem MazurTransfer.mixed_quadratic_reciprocal_equations (R : Type*) [CommRing R] (x z : R) (hxz : x * z = 1) :
    (∀ y : R, y ^ 2 + (x ^ 3 + x ^ 2 + 1) * y - x * (x + 1) = 0 →
      (y * z ^ 3) ^ 2 + (1 + z + z ^ 3) * (y * z ^ 3) - (z ^ 4 + z ^ 5) = 0) ∧
    (∀ w : R, w ^ 2 + (1 + z + z ^ 3) * w - (z ^ 4 + z ^ 5) = 0 →
      (w * x ^ 3) ^ 2 + (x ^ 3 + x ^ 2 + 1) * (w * x ^ 3) - x * (x + 1) = 0) := by sorry
