-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_renewal_gap_algebra_identity_public
-- name    : Kyprianou.Ch08.StageB.p2m81_renewal_gap_algebra_identity_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T04:11:26.949404+00:00
-- url     : https://prove2.me/theorems/d84ebbdc-df86-4676-88d1-55f8e7310d6c
-- title:
--   Gap algebra closes the renewal Laplace ratio
-- statement:
--   For fixed s>0, with R(s).toReal in (0,1] and the gap/kappa formulas, the ENNReal ratio c*R/(1-r) with c=d/f(d) equals s/f(s): at s=d via R/R=1, away from d via f-cancellation using R(s)=f(d)*(d-s)/(d*(f(d)-f(s))).
-- source:
--   Decomposition of Kyprianou.Ch08.StageB.p2m81_geometric_renewal_from_gap (1683b347-a85a-4b0e-b47b-61a14cca75e1): source-faithful public child for code-budget split (167 lines/6157 tokens exceed 100/2500 caps). Pointwise gap algebra closing the renewal Laplace identity; applied per s after the geometric-series child.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_renewal_gap_algebra_identity_public
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (d : ℝ) (hd : 0 < d) (ρ : Measure ℝ)
    (heq : ∀ s : ℝ, 0 < s →
      (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
        f d * (1 - s / d))
    (κ : Measure ℝ)
    (hκgen : ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) =
        ENNReal.ofReal d * (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ)) / ENNReal.ofReal s)
    (hκform : ∀ s : ℝ, 0 < s → s ≠ d →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) =
        ENNReal.ofReal ((s * f d - d * f s) / (s * (f d - f s))))
    (hRpos : ∀ s : ℝ, 0 < s → 0 < (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal)
    (hRle : ∀ s : ℝ, 0 < s → (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal ≤ 1)
    (s : ℝ) (hs : 0 < s) :
    ENNReal.ofReal (d / f d) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) *
      (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ))⁻¹ =
      ENNReal.ofReal (s / f s) := by sorry
