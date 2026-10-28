-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_weighted_integral_quadraticExponent_of_compact_readable
-- name    : FunctionalInequalities.Probability.Posterior.contDiff_weighted_integral_quadraticExponent_of_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:59.808402+00:00
-- url     : https://prove2.me/theorems/4fe89257-70b6-4433-b7b3-1b2d874f4eb1
-- title:
--   Smoothness of the Unnormalized Quadratic-Exponential Integral
-- statement:
--   This statement formalizes the smoothness of the unnormalized posterior integral; it is part of the compact-prior stage preceding Equation (67) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\mu$ be a probability measure with compact support. Let $f:E\to\mathbb R$ be measurable. Let $C\in\mathbb R$ satisfy $0\leq C$, and assume $\|f(x)\|\leq C$ on the support of $\mu$. Fix a continuous linear map $Q:E\to E$.
--
--   The map of the linear parameter $c\in E$ defined by
--
--   $$
--   c\longmapsto\int_E e^{E_{c,Q}(x)}f(x)\,d\mu(x)
--   $$
--
--   is $C^\infty$, where $E_{c,Q}(x)$ is `quadraticExponent c Q x`:
--
--   $$
--   \operatorname{ContDiff}_{\mathbb R}^{\infty}
--   \left(c\mapsto\int_E e^{E_{c,Q}(x)}f(x)\,d\mu(x)\right).
--   $$
--
--   This is an unnormalized-integral regularity result and does not assert regularity in $Q$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiff_weighted_integral_quadraticExponent_of_compact (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
--       {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
--       (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (Q : E →L[ℝ] E) :
--       ContDiff ℝ ∞ (fun c : E => ∫ x, Real.exp (quadraticExponent c Q x) * f x ∂(μ : Measure E))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363).
--
--   Definition modules: [`Probability/Posterior/Exponent`](https://prove2.me/theorems/36c30d18-f69a-4499-bf5e-0d0678b5706c).
--
--   Supporting theorems: [`integrable_exp_norm_mul_of_compact`](https://prove2.me/theorems/93df8d91-b0d9-4aa8-a712-e52703fff899).
--
--   Previous: [`integrable_exp_norm_mul_of_compact`](https://prove2.me/theorems/93df8d91-b0d9-4aa8-a712-e52703fff899) · Next: [`contDiff_posteriorExpectation_c`](https://prove2.me/theorems/ddae5880-1008-4ea8-8902-6d872c26def3).
--
--   [Source excerpt, lines 62–65](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L62-L65) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L60-L89 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Generator`, declaration `FunctionalInequalities.Probability.Posterior.contDiff_weighted_integral_quadraticExponent_of_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.contDiff_weighted_integral_quadraticExponent_of_compact_readable (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (Q : E →L[ℝ] E) :
    ContDiff ℝ ∞ (fun c : E => ∫ x, Real.exp (quadraticExponent c Q x) * f x ∂(μ : Measure E)) := by sorry
