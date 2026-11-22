-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_step_lt
-- name    : Kyprianou.Ch08.StageB.p2m81_drawdown_step_lt
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T01:55:32.523846+00:00
-- url     : https://prove2.me/theorems/102492e6-e2ef-4ce4-b125-d94667e02304
-- title:
--   Drawdown scale strictly increases past one
-- statement:
--   At s=1 the drawdown equation gives (f(d)-f(1))*l1=f(d)*(1-1/d)>0 for d>1, forcing f(1)<f(d) since l1>0. Proved from the Laplace-bounds helper.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_drawdown_step_lt
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
    (d : ℝ) (hd1 : 1 < d) : f 1 < f d := by
  sorry
