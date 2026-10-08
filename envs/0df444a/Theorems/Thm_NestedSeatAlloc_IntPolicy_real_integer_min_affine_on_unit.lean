-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_real_integer_min_affine_on_unit
-- name    : NestedSeatAlloc.IntPolicy.real_integer_min_affine_on_unit
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T16:15:01.370545+00:00
-- url     : https://prove2.me/theorems/9269e88a-1f9d-4e3e-b4e0-a72120112337
-- title:
--   Integer-valued real demand is affine after truncation on each unit interval
-- statement:
--   If a real demand is integer-valued, its fare-scaled truncation is affine on every closed unit interval.
-- source:
--   Source-faithful real-valued integer-demand affine bridge in candidates/eq27_real_integer_min_affine_on_unit.lean; this packages the pointwise branch used by equation (27).

import Mathlib

namespace NestedSeatAlloc.IntPolicy

theorem real_integer_min_affine_on_unit
    (a x : ℝ) (m : ℕ) (hx : ∃ n : ℕ, x = n) :
    ∃ c d : ℝ, ∀ s ∈ Set.Icc (m : ℝ) (m + 1),
      a * min s x = c + d * s := by sorry

end NestedSeatAlloc.IntPolicy
