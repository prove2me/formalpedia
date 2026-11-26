-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41GridMinimumAtZeroV24
-- name    : Kyprianou.Ch04.exercise41GridMinimumAtZeroV24
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:08:05.731011+00:00
-- url     : https://prove2.me/theorems/7634bddd-4ba1-4ef0-bb00-2ba0fffc92e4
-- title:
--   A zero attained strictly inside a nonnegative window gives the exact shifted dense-grid infimum
-- statement:
--   A zero attained strictly inside a nonnegative window gives the exact shifted dense-grid infimum
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41GridMinimumAtZeroV24
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (r s h : NNReal) (hrs : r ≤ s) (hsh : s < r+h)
    (hR : ∀ t, ContinuousWithinAt x (Ici t) t)
    (hMin : ∀ u ∈ Icc r (r+h), 0 ≤ x u) (hz : x s = 0) :
    x r + (⨅ k : ℕ, (x (r + min (q k) h) - x r)) = 0 := by
  sorry
