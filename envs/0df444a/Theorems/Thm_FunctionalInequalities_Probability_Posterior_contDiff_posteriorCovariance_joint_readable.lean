-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorCovariance_joint_readable
-- name    : FunctionalInequalities.Probability.Posterior.contDiff_posteriorCovariance_joint_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:58.550645+00:00
-- url     : https://prove2.me/theorems/a52d87ad-7224-4ad7-973f-f486c36649d8
-- title:
--   Joint Smoothness of the Posterior Covariance Operator
-- statement:
--   This statement formalizes joint smoothness of the posterior covariance operator.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\mu$ be a probability measure with compact support. For each parameter pair $(c,Q)\in E\times(E\to_L E)$, let `compactPosterior μ hc c Q` be the corresponding compact posterior and let `Covariance.operator` denote its covariance operator.
--
--   The operator-valued map
--
--   $$
--   (c,Q)\longmapsto
--   \operatorname{Covariance.operator}(\mu_{c,Q})
--   $$
--
--   is infinitely continuously differentiable in the operator norm:
--
--   $$
--   \operatorname{ContDiff}_{\mathbb R}^{\infty}
--   \left((c,Q)\mapsto\operatorname{Covariance.operator}(\mu_{c,Q})\right).
--   $$
--
--   No isotropy or symmetry assumption on $Q$ is present. The result is a finite-dimensional coordinate reconstruction of the joint covariance regularity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiff_posteriorCovariance_joint (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) :
--       ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
--         Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/JointRegularity`](https://prove2.me/theorems/38b44b15-e229-4b35-89b9-63261754a611).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda).
--
--   Supporting theorems: [`contDiff_covariance_pair_joint`](https://prove2.me/theorems/f0d416e4-4daa-49f4-9fdf-85bc15992dcb).
--
--   Previous: [`contDiff_covariance_pair_joint`](https://prove2.me/theorems/f0d416e4-4daa-49f4-9fdf-85bc15992dcb).
--
--   [Source excerpt, lines 298–301](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/JointRegularity.lean#L298-L301) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/JointRegularity.lean#L296-L325 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.JointRegularity`, declaration `FunctionalInequalities.Probability.Posterior.contDiff_posteriorCovariance_joint`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_JointRegularity

open MeasureTheory ProbabilityTheory FunctionalInequalities
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.contDiff_posteriorCovariance_joint_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E)) := by sorry
