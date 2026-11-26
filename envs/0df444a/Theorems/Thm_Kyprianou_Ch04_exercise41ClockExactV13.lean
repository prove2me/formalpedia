-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41ClockExactV13
-- name    : Kyprianou.Ch04.exercise41ClockExactV13
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:57:47.529937+00:00
-- url     : https://prove2.me/theorems/d177c063-a088-533d-9bc2-826fa266fa42
-- title:
--   Near-zero clock hits an isolated zero exactly under the compact separation condition
-- statement:
--   Near-zero clock hits an isolated zero exactly under the compact separation condition
-- source:
--   Kyprianou (2006), Exercise 4.1(ii) auxiliary result

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41ClockExactV13
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (a s : NNReal) (has : a ≤ s)
    (hr : ContinuousWithinAt x (Ici s) s) (hz : x s = 0)
    (hgap : ∀ b < s, ∃ e : ℝ, 0 < e ∧ ∀ u ∈ Icc a b, e ≤ |x u|) :
    (⨆ n : ℕ, ⨅ k : ℕ, if a ≤ q k ∧ |x (q k)| < 1 / ((n : ℝ) + 1)
      then (q k : WithTop NNReal) else ⊤) = (s : WithTop NNReal) := by
  sorry
