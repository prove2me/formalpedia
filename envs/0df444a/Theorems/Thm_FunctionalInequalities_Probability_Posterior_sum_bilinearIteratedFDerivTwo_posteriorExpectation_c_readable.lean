-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_sum_bilinearIteratedFDerivTwo_posteriorExpectation_c_readable
-- name    : FunctionalInequalities.Probability.Posterior.sum_bilinearIteratedFDerivTwo_posteriorExpectation_c_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:18.579781+00:00
-- url     : https://prove2.me/theorems/2a7c5069-4ad3-4727-be3f-94142fd12abe
-- title:
--   Trace of the Posterior Expectation Hessian
-- statement:
--   This is the trace formula for the posterior expectation Hessian against a symmetric operator.
--
--   Let $E$ be a finite-dimensional complete real inner-product space, let $\mu$ be compactly supported, and let $f$ be measurable and bounded on the support by $C\ge0$. Let $Q,M:E\to E$ be continuous linear maps, let $(b_i)$ be an orthonormal basis indexed by a finite type $\iota$, and assume $M$ is self-adjoint:
--
--   $$\langle Mu,v\rangle=\langle u,Mv\rangle.$$
--
--   For $\nu=\mu.\operatorname{tilted}(\operatorname{quadraticExponent}(c,Q))$ and $a=\operatorname{posteriorMean}(\mu,c,Q)$,
--
--   $$\sum_i D_c^2\mathbb E_{\nu}[f](M b_i,b_i)
--   =\operatorname{Cov}_{\nu}(f,x\mapsto\langle Mx,x\rangle)
--   -2\operatorname{Cov}_{\nu}(f,x\mapsto\langle Ma,x\rangle).$$
--
--   This converts the Hessian contribution into the covariance expression used in the generator calculation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_bilinearIteratedFDerivTwo_posteriorExpectation_c (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
--       {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
--       (c : E) (Q M : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
--       (hM : ∀ u v : E, ⟪M u, v⟫ = ⟪u, M v⟫) :
--       (∑ i, bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c (M (b i)) (b i)) =
--         covariance f (fun x => ⟪M x, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
--           2 * covariance f (fun x => ⟪M (posteriorMean μ c Q), x⟫)
--             ((μ : Measure E).tilted (quadraticExponent c Q))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363).
--
--   Definition modules: [`Probability/Posterior/Exponent`](https://prove2.me/theorems/36c30d18-f69a-4499-bf5e-0d0678b5706c).
--
--   Supporting theorems: [`bilinearIteratedFDerivTwo_posteriorExpectation_c`](https://prove2.me/theorems/7f1d74c8-ab70-45c8-8bf8-3c55be335051), [`exists_uniform_norm_moments_tilted_quadraticExponent_of_compact`](https://prove2.me/theorems/840d9ee9-637c-4b2c-918e-01a3cf6f78a7).
--
--   Previous: [`bilinearIteratedFDerivTwo_posteriorExpectation_c`](https://prove2.me/theorems/7f1d74c8-ab70-45c8-8bf8-3c55be335051).
--
--   [Source excerpt, lines 213–221](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L213-L221) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L211-L273 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Generator`, declaration `FunctionalInequalities.Probability.Posterior.sum_bilinearIteratedFDerivTwo_posteriorExpectation_c`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

theorem FunctionalInequalities.Probability.Posterior.sum_bilinearIteratedFDerivTwo_posteriorExpectation_c_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q M : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (hM : ∀ u v : E, ⟪M u, v⟫ = ⟪u, M v⟫) :
    (∑ i, bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c (M (b i)) (b i)) =
      covariance f (fun x => ⟪M x, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
        2 * covariance f (fun x => ⟪M (posteriorMean μ c Q), x⟫)
          ((μ : Measure E).tilted (quadraticExponent c Q)) := by sorry
