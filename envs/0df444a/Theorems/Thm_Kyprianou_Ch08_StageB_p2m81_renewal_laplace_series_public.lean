-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_renewal_laplace_series_public
-- name    : Kyprianou.Ch08.StageB.p2m81_renewal_laplace_series_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T04:11:28.193101+00:00
-- url     : https://prove2.me/theorems/3b963eef-0c6a-4810-9c52-13d58f4af245
-- title:
--   Renewal sum Laplace is the geometric-series closed form
-- statement:
--   For m(0)=dirac 0, m(n+1)=kappa*m(n) s-finite and nu=sum_n c.(rho*(m n)), Laplace multiplicativity gives Laplace(m(n))=r^n and Laplace(rho*m(n))=R*r^n, so the sum is c*R*sum_n r^n = c*R/(1-r) for every s>0 with r(s)<1.
-- source:
--   Decomposition of Kyprianou.Ch08.StageB.p2m81_geometric_renewal_from_gap (1683b347-a85a-4b0e-b47b-61a14cca75e1): source-faithful public child for code-budget split (167 lines/6157 tokens exceed 100/2500 caps). Series half of the renewal Laplace identity; the real gap algebra closing c*R/(1-r)=s/f(s) is a separate child.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_renewal_laplace_series_public
    (ρ : Measure ℝ) (hprob : IsProbabilityMeasure ρ)
    (κ : Measure ℝ) [SFinite κ]
    (m : ℕ → Measure ℝ) (hm0 : m 0 = Measure.dirac 0)
    (hmsucc : ∀ n : ℕ, m (n + 1) = κ.conv (m n))
    (hsf : ∀ n : ℕ, SFinite (m n))
    (c : ℝ≥0∞) (ν : Measure ℝ)
    (hν : ν = Measure.sum (fun n : ℕ => c • (ρ.conv (m n))))
    (hκlt : ∀ s : ℝ, 0 < s → (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) < 1) :
    ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) =
        c * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) *
          (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ))⁻¹ := by sorry
