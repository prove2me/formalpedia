-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_hasDerivWithinAt_of_affine_interval_right
-- name    : NestedSeatAlloc.IntPolicy.hasDerivWithinAt_of_affine_interval_right
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T15:21:02.41599+00:00
-- url     : https://prove2.me/theorems/b184a71f-b0fa-4810-acef-8cce39923059
-- title:
--   Right derivative of a closed-interval affine function
-- statement:
--   An affine identity on a closed unit interval gives the right within-derivative at every point of that interval.
-- source:
--   Source-faithful arbitrary-point derivative transport in candidates/eq27_affine_interval_one_sided_derivatives.lean; used by equation-(27) strict-tail assembly.

import Mathlib

namespace NestedSeatAlloc.IntPolicy

theorem hasDerivWithinAt_of_affine_interval_right
    {g : ℝ → ℝ} {m : ℕ} {c d s : ℝ}
    (hs : s ∈ Set.Icc (m : ℝ) (m + 1))
    (haff : ∀ t ∈ Set.Icc (m : ℝ) (m + 1), g t = c + d * t) :
    HasDerivWithinAt g d (Set.Ici s) s := by sorry

end NestedSeatAlloc.IntPolicy
