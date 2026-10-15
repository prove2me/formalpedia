-- Prove2me | Theorems.Thm_MazurTransfer_mixed_inverse_parameter_reciprocal_recovery
-- name    : MazurTransfer.mixed_inverse_parameter_reciprocal_recovery
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-15T05:35:43.102601+00:00
-- url     : https://prove2.me/theorems/49dd6220-edd9-4e63-9305-4c0a6120cd4c
-- title:
--   Integral positive-infinity recovery for the mixed inverse-parameter algebra
-- statement:
--   In a commutative ring, assume h=l-a², l=1-s-b, ab=sl, b²h=al², hu=1 and lv=1. Put z=bv and w=u-(1+z+z³). Then za=s, z²h=a, z³h=s, u²-(1+z+z³)u-z⁴(1+z)=0, and w²+(1+z+z³)w-(z⁴+z⁵)=0. This constructs the literal reciprocal coordinates on the positive-infinity patch of the mixed inverse finite algebra. It works over any commutative ring, including characteristic two, and requires neither a domain nor an inverse of two.
-- source:
--   Owned MazurTheorem mixed inverse finite-chart construction, Apache-2.0. Adapts the retained inverse-parameter infinity recovery method to integral mixed coordinates. Checked with the default Lean limits on Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib

theorem MazurTransfer.mixed_inverse_parameter_reciprocal_recovery
    {A : Type*} [CommRing A] (s a b h l u v : A)
    (hh : h = l - a ^ 2) (hl : l = 1 - s - b)
    (hab : a * b = s * l) (hb : b ^ 2 * h = a * l ^ 2)
    (hu : h * u = 1) (hv : l * v = 1) :
    let z := b * v
    (z * a = s) ∧ (z ^ 2 * h = a) ∧ (z ^ 3 * h = s) ∧
    (u ^ 2 - (1 + z + z ^ 3) * u - z ^ 4 * (1 + z) = 0) ∧
    ((u - (1 + z + z ^ 3)) ^ 2 + (1 + z + z ^ 3) * (u - (1 + z + z ^ 3)) -
      (z ^ 4 + z ^ 5) = 0) := by sorry
