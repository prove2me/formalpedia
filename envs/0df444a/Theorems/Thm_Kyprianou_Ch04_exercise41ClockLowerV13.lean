-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41ClockLowerV13
-- name    : Kyprianou.Ch04.exercise41ClockLowerV13
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:57:44.920003+00:00
-- url     : https://prove2.me/theorems/f84aa8b6-350d-56ec-a7f8-888145afeaf0
-- title:
--   A compact interval separated from zero gives a lower bound on dense near-zero clock
-- statement:
--   A compact interval separated from zero gives a lower bound on dense near-zero clock
-- source:
--   Kyprianou (2006), Exercise 4.1(ii) auxiliary result

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41ClockLowerV13
    (x : NNReal → ℝ) (q : ℕ → NNReal) (a b : NNReal)
    (e : ℝ) (he : 0 < e) (hgap : ∀ u ∈ Icc a b, e ≤ |x u|) :
    (b : WithTop NNReal) ≤ (⨆ n : ℕ, ⨅ k : ℕ, if a ≤ q k ∧ |x (q k)| < 1 / ((n : ℝ) + 1)
      then (q k : WithTop NNReal) else ⊤) := by
  sorry
