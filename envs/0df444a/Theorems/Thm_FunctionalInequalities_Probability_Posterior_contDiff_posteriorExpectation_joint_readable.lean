-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorExpectation_joint_readable
-- name    : FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:53.110394+00:00
-- url     : https://prove2.me/theorems/26f7270c-a7c7-4be5-ace6-46911a4ce683
-- title:
--   Joint Smoothness of Compact Posterior Expectations
-- statement:
--   This statement formalizes the joint smoothness assertion associated with Equation (67), p. 19, of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\mu$ be a probability measure with compact support. Let $f:E\to\mathbb R$ be measurable, and suppose there is $C\in\mathbb R$ such that
--
--   $$
--   \|f(x)\|\leq C
--   $$
--
--   for every $x$ in the support of $\mu$. No nonnegativity assumption on $C$ appears in the type.
--
--   Then the map on the product of the linear parameter and operator parameter is infinitely continuously differentiable:
--
--   $$
--   \operatorname{ContDiff}_{\mathbb R}^{\infty}
--   \left((c,Q)\mapsto \operatorname{posteriorExpectation}(\mu,c,Q,f)\right),
--   $$
--
--   for $(c,Q)\in E\times(E\to_L E)$. The result includes arbitrary finite $Q$, including $Q=0$ and nonsymmetric operators, and does not impose isotropy on $\mu$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiff_posteriorExpectation_joint (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
--       {C : ℝ} (hb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) :
--       ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => posteriorExpectation μ p.1 p.2 f)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/JointRegularity`](https://prove2.me/theorems/38b44b15-e229-4b35-89b9-63261754a611).
--
--   Definition modules: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363).
--
--   Supporting theorems: [`contDiff_posteriorExpectation_c`](https://prove2.me/theorems/ddae5880-1008-4ea8-8902-6d872c26def3).
--
--   Next: [`contDiff_posteriorMean_joint`](https://prove2.me/theorems/74843a12-a6a2-460d-9106-3e5347056aaa).
--
--   [Source excerpt, lines 188–191](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/JointRegularity.lean#L188-L191) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/JointRegularity.lean#L184-L206 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.JointRegularity`, declaration `FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_JointRegularity

open MeasureTheory ProbabilityTheory FunctionalInequalities
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => posteriorExpectation μ p.1 p.2 f) := by sorry
