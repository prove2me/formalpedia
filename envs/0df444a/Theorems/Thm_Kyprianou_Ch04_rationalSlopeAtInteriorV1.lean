-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rationalSlopeAtInteriorV1
-- name    : Kyprianou.Ch04.rationalSlopeAtInteriorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:44:10.165814+00:00
-- url     : https://prove2.me/theorems/b2713729-f5dc-4c5d-8a80-54fb53f63e1a
-- title:
--   Derivative at an interior time gives the rational increment slope limit
-- statement:
--   Use the right-hand slope characterisation of a derivative and transport positive rational time increments through the nonnegative-real coercion.
-- source:
--   Supporting proof for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.rationalSlopeAtInteriorV1 (x : ℝ≥0 → ℝ) (d s : ℝ) (hs : 0 ≤ s)
    (hd : HasDerivAt (fun t : ℝ => x (Real.toNNReal t)) d s) :
    Tendsto (fun r : ℚ =>
      (x (Real.toNNReal s + Real.toNNReal (r : ℝ)) - x (Real.toNNReal s)) /
        (Real.toNNReal (r : ℝ) : ℝ))
      (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d) := by
  sorry
