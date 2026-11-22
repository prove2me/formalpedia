-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_gap_kappa_lt_one_of_rho_public
-- name    : Kyprianou.Ch08.StageB.p2m81_gap_kappa_lt_one_of_rho_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T04:11:27.003853+00:00
-- url     : https://prove2.me/theorems/1b71e918-6aa7-4621-a453-ca17eb50c38f
-- title:
--   Gap kernel Laplace is a strict contraction given rho bounds
-- statement:
--   From the gap identity linking R(s) to f and the two kappa Laplace formulas, with R(s) in (0,1], the kappa Laplace r(s) is below 1 for every s>0: at s=d via r=d*(1-R)/d, away from d via the f-ratio with (d-s)/(f(d)-f(s))>0.
-- source:
--   Decomposition of Kyprianou.Ch08.StageB.p2m81_geometric_renewal_from_gap (1683b347-a85a-4b0e-b47b-61a14cca75e1): source-faithful public child for code-budget split (167 lines/6157 tokens exceed 100/2500 caps). Contraction r(s)<1 needed for geometric-series convergence of the renewal Laplace sum.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_gap_kappa_lt_one_of_rho_public
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (d : ℝ) (hd : 0 < d) (ρ : Measure ℝ)
    (heq : ∀ s : ℝ, 0 < s →
      (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
        f d * (1 - s / d))
    (κ : Measure ℝ) [SFinite κ]
    (hκgen : ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) =
        ENNReal.ofReal d * (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ)) / ENNReal.ofReal s)
    (hκform : ∀ s : ℝ, 0 < s → s ≠ d →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) =
        ENNReal.ofReal ((s * f d - d * f s) / (s * (f d - f s))))
    (hR : ∀ s : ℝ, 0 < s →
      0 < (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ∧
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ≤ 1) :
    ∀ s : ℝ, 0 < s → (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) < 1 := by sorry
