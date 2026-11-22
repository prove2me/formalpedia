-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_rho_laplace_pos_le_one_public
-- name    : Kyprianou.Ch08.StageB.p2m81_rho_laplace_pos_le_one_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T04:11:25.444825+00:00
-- url     : https://prove2.me/theorems/7f2688a9-93a1-4c73-a6e9-1b73d1ba3102
-- title:
--   Laplace of a nonneg probability law lies in (0,1]
-- statement:
--   For a probability measure supported on [0,oo), the Laplace transform at any positive rate is strictly positive and at most one, via the a.e. bound exp(-s*y)<=1 on the support and strict positivity of the integrand.
-- source:
--   Decomposition of Kyprianou.Ch08.StageB.p2m81_geometric_renewal_from_gap (1683b347-a85a-4b0e-b47b-61a14cca75e1): source-faithful public child for code-budget split (167 lines/6157 tokens exceed 100/2500 caps). Positivity/boundedness of R(s) used for the gap ratio (d-s)/(f(d)-f(s))>0 and the kappa contraction r(s)<1.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_rho_laplace_pos_le_one_public
    (ρ : Measure ℝ) (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0:ℝ)) = 0) :
    ∀ s : ℝ, 0 < s →
      0 < (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ∧
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ≤ 1 := by sorry
