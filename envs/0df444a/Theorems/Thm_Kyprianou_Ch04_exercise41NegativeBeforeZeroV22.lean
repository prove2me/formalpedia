-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41NegativeBeforeZeroV22
-- name    : Kyprianou.Ch04.exercise41NegativeBeforeZeroV22
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:05:29.922025+00:00
-- url     : https://prove2.me/theorems/ec0abf2c-ca3d-5ce5-9275-964a81fb46c4
-- title:
--   A zero with positive departure and no local minimum has a negative point after any earlier cutoff
-- statement:
--   A zero with positive departure and no local minimum has a negative point after any earlier cutoff
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41NegativeBeforeZeroV22
    (x : NNReal → ℝ) (a s : NNReal) (ha : a < s) (hs : 0 < s) (hz : x s = 0)
    (hDep : ∃ e : NNReal, 0 < e ∧ ∀ u : NNReal, 0 < u → u < e → 0 < x (s+u))
    (hMin : ¬ (∃ e : NNReal, 0 < e ∧ ∀ u ∈ Icc (s-e) (s+e), 0 ≤ x u)) :
    ∃ v ∈ Ioo a s, x v < 0 := by
  sorry
