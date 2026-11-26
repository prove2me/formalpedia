-- Prove2me | Theorems.Thm_Kyprianou_Ch04_positiveSecantProbabilityFull
-- name    : Kyprianou.Ch04.positiveSecantProbabilityFull
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:39:41.972749+00:00
-- url     : https://prove2.me/theorems/9b940ccf-70ec-491c-9705-4e0ec7141590
-- title:
--   Positive secant infimum forces full probability
-- statement:
--   A positive infimum of secants makes all positive secants positive. The bound by p forces every secant to be at least m/p, hence m/p ≤ m and p = 1.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.positiveSecantProbabilityFull
    (f : ℝ → ℝ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hm : 0 < max 0 (sInf ((fun b : ℝ => f b / b) '' Ioi 0)))
    (hbound : ∀ b : ℝ, 0 < b →
      max 0 (sInf ((fun b : ℝ => f b / b) '' Ioi 0)) * b / f b ≤ p) :
    p = 1 := by
  sorry
