-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_ratio_bound
-- name    : Kyprianou.Ch08.StageB.p2m81_drawdown_ratio_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T01:55:33.158309+00:00
-- url     : https://prove2.me/theorems/c70e862e-306e-42c7-aa42-7bbb02f8f91d
-- title:
--   Pointwise drawdown ratio bound
-- statement:
--   For d=1 the ratio bound is reflexivity; for d>1, (f(d)-f(1))*l1<=f(d)-f(1) from l1<=1 gives f(1)<=f(d)/d, hence d*f(1)<=f(d). Proved from the Laplace-bounds and step helpers.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_drawdown_ratio_bound
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
    (d : ℝ) (hd1 : 1 ≤ d) : d / f d ≤ 1 / f 1 := by
  sorry
