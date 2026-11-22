-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_bound_and_vanishing
-- name    : Kyprianou.Ch08.StageB.p2m81_drawdown_bound_and_vanishing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T00:38:58.815395+00:00
-- url     : https://prove2.me/theorems/b4a87593-5018-4f31-8c5e-a43a9da04dda
-- title:
--   Drawdown ratio bound and vanishing singletons
-- statement:
--   Under the per-scale drawdown equations, d/f(d) for d>=1 is bounded by 1/f(1) from the s=1 equation with the probability Laplace cap, and the Laplace deficit at rate one tends to zero, so Markov applied to one minus exp(-Y) sends every fixed positive singleton to zero. Supplies the uniform constant and limit for the atom squeeze.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_drawdown_bound_and_vanishing
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (hdraw : ∀ d : ℝ, 0 < d → ∃ ρ : Measure ℝ,
      IsProbabilityMeasure ρ ∧ ρ (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
          f d * (1 - s / d))
    (ρd : ℝ → Measure ℝ)
    (hρd : ∀ d : ℝ, 0 < d →
      IsProbabilityMeasure (ρd d) ∧ (ρd d) (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂(ρd d)).toReal =
          f d * (1 - s / d)) :
    (∀ d : ℝ, 1 ≤ d → d / f d ≤ 1 / f 1) ∧
    (∀ x : ℝ, 0 < x →
      Tendsto (fun d : ℝ => (ρd d) {x}) atTop (nhds (0 : ℝ≥0∞))) := by
  sorry
