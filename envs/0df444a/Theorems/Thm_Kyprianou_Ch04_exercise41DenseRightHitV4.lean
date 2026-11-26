-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41DenseRightHitV4
-- name    : Kyprianou.Ch04.exercise41DenseRightHitV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:23:19.368189+00:00
-- url     : https://prove2.me/theorems/6bb96110-c080-5834-bc5e-5b013fa0c256
-- title:
--   Right continuity detects each zero by a dense observation inside its half-open cell
-- statement:
--   Right continuity detects each zero by a dense observation inside its half-open cell
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41DenseRightHitV4
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (s : NNReal) (b e : ℝ) (hs : (s : ℝ) < b) (he : 0 < e)
    (hr : ContinuousWithinAt x (Ici s) s) (hz : x s = 0) :
    ∃ k : ℕ, s ≤ q k ∧ (q k : ℝ) < b ∧ |x (q k)| < e  := by
  sorry
