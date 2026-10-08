-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_hasDerivWithinAt_of_affine_interval_left
-- name    : NestedSeatAlloc.IntPolicy.hasDerivWithinAt_of_affine_interval_left
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T15:20:56.853298+00:00
-- url     : https://prove2.me/theorems/ef24f6e6-1cab-4f2a-936d-724d64058d07
-- title:
--   Left derivative of a closed-interval affine function
-- statement:
--   An affine identity on a closed unit interval gives the left within-derivative at every point of that interval.
-- source:
--   Source-faithful arbitrary-point derivative transport in candidates/eq27_affine_interval_one_sided_derivatives.lean; used by equation-(27) non-strict-tail assembly.

import Mathlib

namespace NestedSeatAlloc.IntPolicy

theorem hasDerivWithinAt_of_affine_interval_left
    {g : ℝ → ℝ} {m : ℕ} {c d s : ℝ}
    (hs : s ∈ Set.Icc ((m : ℝ) - 1) (m : ℝ))
    (haff : ∀ t ∈ Set.Icc ((m : ℝ) - 1) (m : ℝ), g t = c + d * t) :
    HasDerivWithinAt g d (Set.Iic s) s := by sorry

end NestedSeatAlloc.IntPolicy
