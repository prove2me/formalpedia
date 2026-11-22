-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_geometric_renewal_from_gap
-- name    : Kyprianou.Ch08.StageB.p2m81_geometric_renewal_from_gap
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T00:39:00.605801+00:00
-- url     : https://prove2.me/theorems/1683b347-a85a-4b0e-b47b-61a14cca75e1
-- title:
--   One-scale potential from tail kernel data
-- statement:
--   From tail kernel data at one scale, the geometric renewal sum has Laplace one over one minus the kernel transform, is supported on the half-line and finite on lower intervals. Convolving with the drawdown law and scaling by d/f(d) gives a potential with Laplace s/f(s); the diagonal s=d case follows from the general kernel identity, and all positive atoms come from the renewal zeroth term. Proved from the Proved convolution-power, geometric-sum and support helpers.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_geometric_renewal_from_gap
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (d : ℝ) (hd : 0 < d) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0 : ℝ)) = 0)
    (heq : ∀ s : ℝ, 0 < s →
      (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
        f d * (1 - s / d))
    (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (hκatom : ∀ x : ℝ, κ {x} = 0)
    (hκgen : ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) =
        ENNReal.ofReal d * (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ)) / ENNReal.ofReal s)
    (hκform : ∀ s : ℝ, 0 < s → s ≠ d →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) =
        ENNReal.ofReal ((s * f d - d * f s) / (s * (f d - f s))))
    (L : ℝ → ℝ≥0∞)
    (hL : ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) = L s)
    (s0 : ℝ) (hs0 : 0 < s0) (hr : L s0 < 1) :
    ∃ ν : Measure ℝ, ν (Iio (0 : ℝ)) = 0 ∧
      (∀ x : ℝ, 0 ≤ x → ν (Iic x) < ⊤) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) =
          ENNReal.ofReal (s / f s)) ∧
      (∀ x : ℝ, 0 < x → ν {x} = ENNReal.ofReal (d / f d) * ρ {x}) := by
  sorry
