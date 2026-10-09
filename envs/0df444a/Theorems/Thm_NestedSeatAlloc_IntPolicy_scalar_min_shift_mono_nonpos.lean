-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_scalar_min_shift_mono_nonpos
-- name    : NestedSeatAlloc.IntPolicy.scalar_min_shift_mono_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:42:55.659115+00:00
-- url     : https://prove2.me/theorems/3d28b15b-8d51-4116-9fb9-ed5d6eb1457d
-- title:
--   Minimum-minus-capacity multiplied by a nonpositive fare is monotone
-- statement:
--   Pure algebraic monotonicity for nonpositive scalar c:
--   the function s -> c*(min(s,y)-s) is nondecreasing in s.
--   This is the pointwise minimum-shift inequality required for a
--   global expected-revenue shift monotonicity argument when f(1)<=0.
--   Together with a derivative from SubdiffCondition (20), the
--   result can help prove f(1)>0 is necessary for the full
--   general Theorem 1 assumptions.
--
--   No model assumptions, probability, integrability or Lean
--   compilation enter this pure algebraic helper. Verify by Prove2Me.
-- source:
--   Pure algebraic monotonicity for nonpositive scalar c:
--   the function s -> c*(min(s,y)-s) is nondecreasing in s.
--   This is the pointwise minimum-shift inequality required for a
--   global expected-revenue shift monotonicity argument when f(1)<=0.
--   Together with a derivative from SubdiffCondition (20), the
--   result can help prove f(1)>0 is necessary for the full
--   general Theorem 1 assumptions.
--
--   No model assumptions, probability, integrability or Lean
--   compilation enter this pure algebraic helper. Verify by Prove2Me.

import Mathlib

theorem NestedSeatAlloc.IntPolicy.scalar_min_shift_mono_nonpos (c s t y : ℝ) (hc : c ≤ 0)
    (hst : s ≤ t) :
    c * min s y - c * s ≤ c * min t y - c * t := by sorry
