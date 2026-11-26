-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41ClockCoverV14
-- name    : Kyprianou.Ch04.exercise41ClockCoverV14
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:01:53.852042+00:00
-- url     : https://prove2.me/theorems/718f27e3-f581-4dc7-a104-8dcf6fa38983
-- title:
--   The countable capped near-zero clocks cover every zero on a cadlag path with locally finite zeros
-- statement:
--   The countable capped near-zero clocks cover every zero on a cadlag path with locally finite zeros
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41ClockCoverV14
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (hR : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hL : ∀ s, 0 < s → ∃ l, Tendsto x (nhdsWithin s (Iio s)) (nhds l))
    (hNoJump : ∀ s, 0 < s → Function.leftLim x s = 0 → x s = 0)
    (hVisits : ∀ t, Set.Finite {u : NNReal | 0 < u ∧ u ≤ t ∧ x u = 0}) :
    let raw (j : ℕ) : WithTop NNReal := ⨆ n : ℕ, ⨅ k : ℕ,
      if q j ≤ q k ∧ |x (q k)| < 1 / ((n : ℝ) + 1) then (q k : WithTop NNReal) else ⊤
    ∀ s : NNReal, x s = 0 → ∃ j N : ℕ,
      (min (raw j) ((N : NNReal) : WithTop NNReal)).untopD 0 = s := by
  sorry
