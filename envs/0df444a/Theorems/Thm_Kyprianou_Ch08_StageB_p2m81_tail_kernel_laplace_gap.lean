-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_laplace_gap
-- name    : Kyprianou.Ch08.StageB.p2m81_tail_kernel_laplace_gap
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T00:39:00.00107+00:00
-- url     : https://prove2.me/theorems/15634117-9988-4944-84fd-3d20bc3df5d3
-- title:
--   Tail kernel Laplace identity with a strict gap point
-- statement:
--   For a drawdown law at scale d, the tail kernel with density d times rho((x,infty)) on x>0 is s-finite, supported on the nonnegative half-line and atomless. Its Laplace transform equals d times one minus the drawdown Laplace over s for every positive s, hence the closed f-formula away from s=d via the drawdown equation, and it sits strictly below one at some positive rate. Supplies the exact kernel data the one-scale renewal assembly needs.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_tail_kernel_laplace_gap
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (d : ℝ) (hd : 0 < d) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0 : ℝ)) = 0)
    (heq : ∀ s : ℝ, 0 < s →
      (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
        f d * (1 - s / d)) :
    ∃ κ : Measure ℝ, SFinite κ ∧ κ (Iio (0 : ℝ)) = 0 ∧ (∀ x : ℝ, κ {x} = 0) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) =
          ENNReal.ofReal d * (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ)) / ENNReal.ofReal s) ∧
      (∀ s : ℝ, 0 < s → s ≠ d →
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) =
          ENNReal.ofReal ((s * f d - d * f s) / (s * (f d - f s)))) ∧
      (∃ s0 : ℝ, 0 < s0 ∧
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s0 * y)) ∂κ) < 1) := by
  sorry
