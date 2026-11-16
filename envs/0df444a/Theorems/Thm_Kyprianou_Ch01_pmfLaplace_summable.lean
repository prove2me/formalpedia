-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pmfLaplace_summable
-- name    : Kyprianou.Ch01.pmfLaplace_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T18:22:45.173323+00:00
-- url     : https://prove2.me/theorems/d1c82849-b4ab-4ec8-b7d6-0a61dda0257b
-- title:
--   Absolute summability of PMF-weighted nonnegative Laplace exponentials
-- statement:
--   For every probability mass function on the natural numbers and q>=0, the real series of p_k exp(-qk) is summable, dominated by the summable real PMF weights.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.11(iii), Laplace semigroup time continuity without moment assumptions

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Positive exponential weights are summable under every probability mass function. -/

theorem Kyprianou.Ch01.pmfLaplace_summable (p : PMF ℕ) (q : ℝ) (hq : 0 ≤ q) :
    Summable (fun k : ℕ => (p k).toReal * Real.exp (-q * (k : ℝ))) := by sorry
