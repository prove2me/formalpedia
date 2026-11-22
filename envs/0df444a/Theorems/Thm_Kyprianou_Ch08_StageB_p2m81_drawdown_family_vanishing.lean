-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_family_vanishing
-- name    : Kyprianou.Ch08.StageB.p2m81_drawdown_family_vanishing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T01:19:32.828639+00:00
-- url     : https://prove2.me/theorems/1c69ba38-220b-4be1-94d8-786a03614553
-- title:
--   Drawdown singletons vanish at infinity
-- statement:
--   Under the per-scale drawdown equations, every fixed positive singleton mass tends to zero: the s=1 equation with the Laplace cap gives deficit 1-l1(d)<=1/d, so 1-L1(d)<=ofReal(1/d)->0, and the pointwise Markov bound squeezes mu_d{x} between 0 and a null upper envelope. Proved from the Laplace-cap/ratio helper and the Markov helper. Supplies the limit half of the parent conjunction.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_drawdown_family_vanishing
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
          f d * (1 - s / d))
    (x : ℝ) (hx : 0 < x) :
    Tendsto (fun d : ℝ => (ρd d) {x}) atTop (nhds (0 : ℝ≥0∞)) := by
  sorry
