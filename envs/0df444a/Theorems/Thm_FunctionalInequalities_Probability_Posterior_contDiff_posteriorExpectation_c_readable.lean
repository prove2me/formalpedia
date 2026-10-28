-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorExpectation_c_readable
-- name    : FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_c_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:04.853014+00:00
-- url     : https://prove2.me/theorems/ddae5880-1008-4ea8-8902-6d872c26def3
-- title:
--   Smoothness of Posterior Expectation in the Linear Parameter
-- statement:
--   This statement formalizes smoothness in the linear parameter for the compact posterior and is partially related to Equation (67), p. 19, of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\mu$ be a compactly supported probability measure. Let $f:E\to\mathbb R$ be measurable, let $C\in\mathbb R$ satisfy $0\leq C$, and assume $\|f(x)\|\leq C$ on the support of $\mu$. Fix a continuous linear map $Q:E\to E$.
--
--   Then the posterior expectation `posteriorExpectation μ c Q f` is infinitely continuously differentiable as a function of $c\in E$:
--
--   $$
--   \operatorname{ContDiff}_{\mathbb R}^{\infty}
--   \left(c\mapsto \operatorname{posteriorExpectation}(\mu,c,Q,f)\right).
--   $$
--
--   The assertion includes $Q=0$ and does not require symmetry of $Q$. It concerns only the $c$ variable, with $Q$ fixed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiff_posteriorExpectation_c (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
--       {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
--       (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (Q : E →L[ℝ] E) :
--       ContDiff ℝ ∞ (fun c => posteriorExpectation μ c Q f)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363).
--
--   Supporting theorems: [`contDiff_weighted_integral_quadraticExponent_of_compact`](https://prove2.me/theorems/4fe89257-70b6-4433-b7b3-1b2d874f4eb1).
--
--   Previous: [`contDiff_weighted_integral_quadraticExponent_of_compact`](https://prove2.me/theorems/4fe89257-70b6-4433-b7b3-1b2d874f4eb1) · Next: [`fderiv_posteriorExpectation_c_apply`](https://prove2.me/theorems/7e365baf-6866-48b0-8974-871a453169bb).
--
--   [Source excerpt, lines 92–95](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L92-L95) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L91-L110 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Generator`, declaration `FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_c`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_c_readable (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (Q : E →L[ℝ] E) :
    ContDiff ℝ ∞ (fun c => posteriorExpectation μ c Q f) := by sorry
