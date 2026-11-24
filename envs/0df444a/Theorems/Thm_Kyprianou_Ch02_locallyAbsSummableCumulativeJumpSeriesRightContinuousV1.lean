-- Prove2me | Theorems.Thm_Kyprianou_Ch02_locallyAbsSummableCumulativeJumpSeriesRightContinuousV1
-- name    : Kyprianou.Ch02.locallyAbsSummableCumulativeJumpSeriesRightContinuousV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:15:50.331934+00:00
-- url     : https://prove2.me/theorems/6577b5f5-dfa1-4f7a-a90c-d27a6b6e7e16
-- title:
--   Locally absolutely summable cumulative jump series is right continuous
-- statement:
--   Truncate the marks to Ioc 0 (t+1), producing a globally absolutely summable atomic series. Apply the existing Proved right-limit theorem for globally summable marks, identify the series on the neighbourhood, and extend the right-sided limit to Ici t.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.12; local absolutely summable cumulative series and right continuity

import Mathlib
open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.locallyAbsSummableCumulativeJumpSeriesRightContinuousV1
    (g : ℝ≥0 → ℝ)
    (hs : ∀ T : ℝ≥0, Summable (fun s : Set.Ioc (0 : ℝ≥0) T => |g s|))
    (t : ℝ≥0) :
    ContinuousWithinAt (fun u : ℝ≥0 =>
      ∑' s : Set.Ioc (0 : ℝ≥0) u, g s) (Ici t) t := by
  sorry
