-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteAffineLeftRightTimeIntegralV1
-- name    : Kyprianou.Ch04.finiteAffineLeftRightTimeIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:46:46.249891+00:00
-- url     : https://prove2.me/theorems/22dc95ba-47ca-5dbd-9a5b-a88db7868ee7
-- title:
--   Left and right finite affine paths have equal time integrals
-- statement:
--   The two finite affine paths differ only at the finite set of retained jump times, which is Lebesgue null.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteAffineLeftRightTimeIntegralV1 (S : Finset NNReal) (j : NNReal → ℝ) (d : ℝ)
    (f : ℝ → ℝ → ℝ) (T : ℝ) :
    (∫ u in Icc (0 : ℝ) T,
      f u (d*u + ∑ r ∈ S, if (r : ℝ) ≤ u then j r else 0)) =
    ∫ u in Icc (0 : ℝ) T,
      f u (d*u + ∑ r ∈ S, if (r : ℝ) < u then j r else 0) := by
  sorry
end Kyprianou.Ch04
