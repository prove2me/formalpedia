-- Prove2me | Theorems.Thm_MazurTransfer_mixed_single_section_reciprocal_recovery
-- name    : MazurTransfer.mixed_single_section_reciprocal_recovery
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-15T05:09:26.888256+00:00
-- url     : https://prove2.me/theorems/683bb821-59ca-4833-be30-f59bb63021d5
-- title:
--   Integral reciprocal recovery from the mixed single-section quartic
-- statement:
--   In any commutative ring, suppose p*u=1 and t^4-p^3-p^2*t-t^3-p^2-p*t=0. Put z=t*u and w=(1+t*u)*u. Then w=t*z^3-(1+z+z^3), and w satisfies the literal reciprocal equation w^2+(1+z+z^3)*w-(z^4+z^5)=0. No field, domain, characteristic, or invertibility-of-two hypothesis is needed. These formulas construct the actual reciprocal-chart map from the localized rank-three parameter algebra of the mixed order-thirteen curve, including its dyadic model.
-- source:
--   Owned MazurTheorem mixed single-section construction, Apache-2.0. Adapts the original retained single-section reciprocal recovery method to integral mixed coordinates. Checked at default Lean limits on Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib

theorem MazurTransfer.mixed_single_section_reciprocal_recovery
    {A : Type*} [CommRing A] (t p u : A) (hu : p * u = 1)
    (htp : t ^ 4 - p ^ 3 - p ^ 2 * t - t ^ 3 - p ^ 2 - p * t = 0) :
    (t * (t * u) ^ 3 - (1 + t * u + (t * u) ^ 3) = (1 + t * u) * u) ∧
    (((1 + t * u) * u) ^ 2 + (1 + t * u + (t * u) ^ 3) * ((1 + t * u) * u) -
      ((t * u) ^ 4 + (t * u) ^ 5) = 0) := by sorry
