-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_conditional_concavity_nonnegative_sum
-- name    : NestedSeatAlloc.IntPolicy.conditional_concavity_nonnegative_sum
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T14:01:05.624619+00:00
-- url     : https://prove2.me/theorems/3271abe1-9182-4946-8b1f-6acbe79c3d87
-- title:
--   Conditional-concavity induction algebra for nonnegative sums
-- statement:
--   A nonnegative linear combination of two concave real-valued seat-level functions is concave on their common convex domain.
-- source:
--   Source-faithful algebraic helper for the theorem1 conditional-revenue concavity induction; it exposes the nonnegative-sum closure needed after the model-specific one-step decomposition.

import Mathlib

namespace NestedSeatAlloc.IntPolicy

theorem conditional_concavity_nonnegative_sum {u v : ℝ → ℝ} {s : Set ℝ}
    (hu : ConcaveOn ℝ s u) (hv : ConcaveOn ℝ s v)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ConcaveOn ℝ s (fun x => a * u x + b * v x) := by sorry

end NestedSeatAlloc.IntPolicy
