-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_fderiv_posteriorExpectation_c_apply_readable
-- name    : FunctionalInequalities.Probability.Posterior.fderiv_posteriorExpectation_c_apply_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:06.715199+00:00
-- url     : https://prove2.me/theorems/7e365baf-6866-48b0-8974-871a453169bb
-- title:
--   Posterior Expectation Derivative in the Linear Parameter
-- statement:
--   This is the $c$-direction derivative formula for a compact posterior expectation.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $\mu$ be a probability measure with compact support, let $f:E\to\mathbb R$ be measurable, and assume that for some $C\ge0$, $\lVert f(x)\rVert\le C$ on $\operatorname{supp}\mu$. For $c,h\in E$ and a continuous linear map $Q:E\to E$, the Fréchet derivative of
--
--   $$y\longmapsto \operatorname{posteriorExpectation}(\mu,y,Q,f)$$
--
--   at $c$, applied to $h$, is
--
--   $$D_c\,\mathbb E_{\mu_{c,Q}}[f](h)
--   =\operatorname{Cov}_{\mu_{c,Q}}\bigl(f,x\mapsto\langle h,x\rangle\bigr),$$
--
--   where $\mu_{c,Q}$ is the measure `μ.tilted (quadraticExponent c Q)`. This is the gradient component of the deterministic posterior generator formalization.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem fderiv_posteriorExpectation_c_apply (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
--       {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
--       (c : E) (Q : E →L[ℝ] E) (h : E) :
--       fderiv ℝ (fun y => posteriorExpectation μ y Q f) c h =
--         covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363).
--
--   Definition modules: [`Probability/Posterior/Exponent`](https://prove2.me/theorems/36c30d18-f69a-4499-bf5e-0d0678b5706c).
--
--   Supporting theorems: [`contDiff_posteriorExpectation_c`](https://prove2.me/theorems/ddae5880-1008-4ea8-8902-6d872c26def3), [`expectation_hasDerivAt_of_compact`](https://prove2.me/theorems/33fce4ba-fea7-459e-923c-b736676bd849).
--
--   Previous: [`contDiff_posteriorExpectation_c`](https://prove2.me/theorems/ddae5880-1008-4ea8-8902-6d872c26def3) · Next: [`bilinearIteratedFDerivTwo_posteriorExpectation_c`](https://prove2.me/theorems/7f1d74c8-ab70-45c8-8bf8-3c55be335051).
--
--   [Source excerpt, lines 118–123](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L118-L123) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L117-L136 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Generator`, declaration `FunctionalInequalities.Probability.Posterior.fderiv_posteriorExpectation_c_apply`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.fderiv_posteriorExpectation_c_apply_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q : E →L[ℝ] E) (h : E) :
    fderiv ℝ (fun y => posteriorExpectation μ y Q f) c h =
      covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) := by sorry
