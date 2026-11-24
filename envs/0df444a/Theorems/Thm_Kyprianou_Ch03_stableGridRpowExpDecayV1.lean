-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableGridRpowExpDecayV1
-- name    : Kyprianou.Ch03.stableGridRpowExpDecayV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T18:19:10.590832+00:00
-- url     : https://prove2.me/theorems/ed87f597-6832-444c-a556-f0a72260c723
-- title:
--   Exponential decay of the scaled stable grid bound
-- statement:
--   For index greater than one, the grid Laplace upper bound converges to zero.
-- source:
--   Auxiliary analytic lemma for Kyprianou (2006), Exercise 3.7.

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

theorem Kyprianou.Ch03.stableGridRpowExpDecayV1 (α c : ℝ) (hα : 1 < α) (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-c * ((n : ℝ) + 1) ^ (1 - 1 / α))) atTop (𝓝 0) := by sorry
