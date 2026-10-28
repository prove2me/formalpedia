-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_bilinearIteratedFDerivTwo_posteriorExpectation_c_readable
-- name    : FunctionalInequalities.Probability.Posterior.bilinearIteratedFDerivTwo_posteriorExpectation_c_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:05.382785+00:00
-- url     : https://prove2.me/theorems/7f1d74c8-ab70-45c8-8bf8-3c55be335051
-- title:
--   Posterior Expectation Hessian in the Linear Parameter
-- statement:
--   This is the $c$-Hessian formula for a compact posterior expectation.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $\mu$ be a compactly supported probability measure, and let $f:E\to\mathbb R$ be measurable and bounded on the support by $C\ge0$. For $c,h,k\in E$ and a continuous linear map $Q$, let $\nu=\mu.\operatorname{tilted}(\operatorname{quadraticExponent}(c,Q))$. Then
--
--   $$D_c^2\mathbb E_{\nu}[f](h,k)
--   =\operatorname{Cov}_{\nu}\bigl(f,x\mapsto\langle h,x\rangle\langle k,x\rangle\bigr)
--   -\left(\int\langle h,x\rangle\,d\nu\right)\operatorname{Cov}_{\nu}\bigl(f,\langle k,x\rangle\bigr)
--   -\left(\int\langle k,x\rangle\,d\nu\right)\operatorname{Cov}_{\nu}\bigl(f,\langle h,x\rangle\bigr).$$
--
--   Here `bilinearIteratedFDerivTwo` is the bilinear second derivative. The identity is the second-order deterministic ingredient for the posterior generator.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem bilinearIteratedFDerivTwo_posteriorExpectation_c (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
--       {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
--       (c : E) (Q : E →L[ℝ] E) (h k : E) :
--       bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c h k =
--         covariance f (fun x => ⟪h, x⟫ * ⟪k, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
--           (∫ x, ⟪h, x⟫ ∂((μ : Measure E).tilted (quadraticExponent c Q))) *
--             covariance f (fun x => ⟪k, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
--           (∫ x, ⟪k, x⟫ ∂((μ : Measure E).tilted (quadraticExponent c Q))) *
--             covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363).
--
--   Definition modules: [`Probability/Posterior/Exponent`](https://prove2.me/theorems/36c30d18-f69a-4499-bf5e-0d0678b5706c).
--
--   Supporting theorems: [`contDiff_posteriorExpectation_c`](https://prove2.me/theorems/ddae5880-1008-4ea8-8902-6d872c26def3), [`covariance_hasDerivAt_of_compact`](https://prove2.me/theorems/9b3908cf-2697-4638-b0df-be6209e77920), [`fderiv_posteriorExpectation_c_apply`](https://prove2.me/theorems/7e365baf-6866-48b0-8974-871a453169bb).
--
--   Previous: [`fderiv_posteriorExpectation_c_apply`](https://prove2.me/theorems/7e365baf-6866-48b0-8974-871a453169bb) · Next: [`sum_bilinearIteratedFDerivTwo_posteriorExpectation_c`](https://prove2.me/theorems/2a7c5069-4ad3-4727-be3f-94142fd12abe).
--
--   [Source excerpt, lines 139–148](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L139-L148) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L138-L169 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Generator`, declaration `FunctionalInequalities.Probability.Posterior.bilinearIteratedFDerivTwo_posteriorExpectation_c`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.bilinearIteratedFDerivTwo_posteriorExpectation_c_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q : E →L[ℝ] E) (h k : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c h k =
      covariance f (fun x => ⟪h, x⟫ * ⟪k, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
        (∫ x, ⟪h, x⟫ ∂((μ : Measure E).tilted (quadraticExponent c Q))) *
          covariance f (fun x => ⟪k, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
        (∫ x, ⟪k, x⟫ ∂((μ : Measure E).tilted (quadraticExponent c Q))) *
          covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) := by sorry
