-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41NoLocalMinimumFromNullWindowsV25
-- name    : Kyprianou.Ch04.exercise41NoLocalMinimumFromNullWindowsV25
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T15:08:54.251992+00:00
-- url     : https://prove2.me/theorems/a4345eaf-6981-4b2d-9ac9-862e2d650ab5
-- title:
--   Null occupation of zero window minima excludes positive-time zero local minima
-- statement:
--   Null occupation of zero window minima excludes positive-time zero local minima
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41NoLocalMinimumFromNullWindowsV25
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (hR : ∀ t, ContinuousWithinAt x (Ici t) t)
    (hNull : ∀ j : ℕ, volume {r : ℝ | 0 ≤ r ∧ x r.toNNReal +
      (⨅ k : ℕ, (x (r.toNNReal+min (q k) (q j)) - x r.toNNReal)) = 0} = 0) :
    ∀ s : NNReal, 0 < s → x s = 0 →
      ¬ (∃ e : NNReal, 0 < e ∧ ∀ u ∈ Icc (s-e) (s+e), 0 ≤ x u) := by
  sorry
