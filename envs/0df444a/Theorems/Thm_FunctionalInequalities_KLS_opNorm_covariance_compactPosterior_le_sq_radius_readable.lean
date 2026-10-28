-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_opNorm_covariance_compactPosterior_le_sq_radius_readable
-- name    : FunctionalInequalities.KLS.opNorm_covariance_compactPosterior_le_sq_radius_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:39.925281+00:00
-- url     : https://prove2.me/theorems/becefc49-e2fe-406f-a71d-0f8f1d8fbe46
-- title:
--   Posterior Covariance Operator Radius Bound
-- statement:
--   This formalizes a covariance-radius estimate related to the compact posterior stage before Equation (67) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a finite-dimensional real inner-product space, let $\mu$ be a probability law with compact support, and let $r\ge0$. Assume
--
--   $$
--   \operatorname{supp}(\mu)\subseteq\overline{B}(0,r).
--   $$
--
--   For arbitrary $c\in E$ and continuous linear $Q:E\to E$, let $\mu_{c,Q}$ be the compact posterior. Then the operator norm of its covariance operator satisfies
--
--   $$
--   \left\|\operatorname{Cov}(\mu_{c,Q})\right\|\le r^2.
--   $$
--
--   The estimate bounds posterior covariance uniformly in the finite parameters $c$ and $Q$ whenever the prior is supported in a ball of radius $r$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem opNorm_covariance_compactPosterior_le_sq_radius (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) {r : ℝ} (hr : 0 ≤ r)
--       (hsupp : (μ : Measure E).support ⊆ Metric.closedBall (0 : E) r) (c : E) (Q : E →L[ℝ] E) :
--       ‖Covariance.operator (compactPosterior μ hc c Q : Measure E)‖ ≤ r ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Posterior/Covariance`](https://prove2.me/theorems/cf6ff972-6f6d-497d-a1ff-ea269ff919aa).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda).
--
--   Supporting theorems: [`covariance_sq_le_variance_mul_variance`](https://prove2.me/theorems/12e81134-7f94-480d-a9f0-74ef2af40616).
--
--   [Source excerpt, lines 173–176](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Posterior/Covariance.lean#L173-L176) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Posterior/Covariance.lean#L170-L282 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Posterior.Covariance`, declaration `FunctionalInequalities.KLS.opNorm_covariance_compactPosterior_le_sq_radius`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance

open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.opNorm_covariance_compactPosterior_le_sq_radius_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure E).support ⊆ Metric.closedBall (0 : E) r) (c : E) (Q : E →L[ℝ] E) :
    ‖Covariance.operator (compactPosterior μ hc c Q : Measure E)‖ ≤ r ^ 2 := by sorry
