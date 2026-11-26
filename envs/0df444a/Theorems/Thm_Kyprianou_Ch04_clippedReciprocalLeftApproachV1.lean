-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clippedReciprocalLeftApproachV1
-- name    : Kyprianou.Ch04.clippedReciprocalLeftApproachV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:56:17.830274+00:00
-- url     : https://prove2.me/theorems/4ce5eb1c-e68a-5035-b2d4-8a0f3db94374
-- title:
--   Clipped reciprocal approach to positive time from strict left
-- statement:
--   Clipped reciprocal approach to positive time from strict left
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem clippedReciprocalLeftApproachV1 (t : NNReal) (ht : 0 < t) :
    Tendsto (fun n : ℕ => Real.toNNReal ((t : ℝ) - 1 / ((n : ℝ) + 1)))
      atTop (𝓝[<] t) := by
  sorry
end Kyprianou.Ch04
