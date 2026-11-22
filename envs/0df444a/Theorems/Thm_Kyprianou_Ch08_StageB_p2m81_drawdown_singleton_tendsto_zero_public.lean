-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_singleton_tendsto_zero_public
-- name    : Kyprianou.Ch08.StageB.p2m81_drawdown_singleton_tendsto_zero_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T18:48:34.696853+00:00
-- url     : https://prove2.me/theorems/7355004d-e477-4997-a89c-d0c1f28649de
-- title:
--   Drawdown singleton masses tend to zero at large scale
-- statement:
--   For the drawdown probability chosen at scale d, its Laplace transform at rate one tends to one as d tends to infinity. Markov's inequality applied to one minus exp(-Y) then bounds any fixed positive singleton mass by the Laplace deficit divided by one minus exp(-x), so the singleton masses tend to zero.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1. Public helper for the geometric descending potential, drawdown singleton limit.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_drawdown_singleton_tendsto_zero_public
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (hdraw : ∀ d : ℝ, 0 < d → ∃ ρ : Measure ℝ,
      IsProbabilityMeasure ρ ∧ ρ (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
          f d * (1 - s / d))
    (x : ℝ) (hx : 0 < x) :
    Tendsto
      (fun d : ℝ =>
        ((if hd : 0 < d then Classical.choose (hdraw d hd) else 0) : Measure ℝ) ({x} : Set ℝ))
      atTop (nhds (0 : ENNReal)) := by
  sorry
