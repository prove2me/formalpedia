-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_L1_cap_and_ratio_bound
-- name    : Kyprianou.Ch08.StageB.p2m81_drawdown_L1_cap_and_ratio_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T01:19:32.168734+00:00
-- url     : https://prove2.me/theorems/fa315679-459a-4389-829b-91cac56faed6
-- title:
--   Drawdown Laplace cap, strict step and ratio bound
-- statement:
--   For the per-scale drawdown laws, the rate-one Laplace value satisfies L1<=1 with 0<l1<=1 from the half-line support cap and everywhere-positive integrand; the s=1 equation then forces f(1)<f(d) for d>1 and, with l1<=1, the ratio bound d/f(d)<=1/f(1) for d>=1. Supplies the uniform constant and the Laplace facts the vanishing argument needs.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_drawdown_L1_cap_and_ratio_bound
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
    (∀ d : ℝ, 0 < d →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d)) ≤ 1 ∧
      0 < ((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d)).toReal) ∧
      ((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d)).toReal) ≤ 1) ∧
    (∀ d : ℝ, 1 < d → f 1 < f d) ∧
    (∀ d : ℝ, 1 ≤ d → d / f d ≤ 1 / f 1) := by
  sorry
