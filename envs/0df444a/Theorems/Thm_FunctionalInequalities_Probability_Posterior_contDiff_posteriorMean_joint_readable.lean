-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorMean_joint_readable
-- name    : FunctionalInequalities.Probability.Posterior.contDiff_posteriorMean_joint_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:56.758724+00:00
-- url     : https://prove2.me/theorems/74843a12-a6a2-460d-9106-3e5347056aaa
-- title:
--   Joint Smoothness of the Posterior Mean
-- statement:
--   This statement proves joint smoothness of the posterior mean in the compact-prior setting.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\mu$ be a probability measure with compact support. For each $(c,Q)\in E\times(E\to_L E)$, let `posteriorMean μ c Q` denote the mean of the corresponding posterior.
--
--   The vector-valued map
--
--   $$
--   (c,Q)\longmapsto \operatorname{posteriorMean}(\mu,c,Q)
--   $$
--
--   is infinitely continuously differentiable:
--
--   $$
--   \operatorname{ContDiff}_{\mathbb R}^{\infty}
--   \left((c,Q)\mapsto\operatorname{posteriorMean}(\mu,c,Q)\right).
--   $$
--
--   This result applies to every finite operator parameter, including nonsymmetric $Q$ and $Q=0$, without an isotropy assumption.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiff_posteriorMean_joint (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) :
--       ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => posteriorMean μ p.1 p.2)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/JointRegularity`](https://prove2.me/theorems/38b44b15-e229-4b35-89b9-63261754a611).
--
--   Definition modules: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363).
--
--   Supporting theorems: [`contDiff_posteriorExpectation_joint`](https://prove2.me/theorems/26f7270c-a7c7-4be5-ace6-46911a4ce683), [`exists_uniform_norm_moments_tilted_quadraticExponent_of_compact`](https://prove2.me/theorems/840d9ee9-637c-4b2c-918e-01a3cf6f78a7).
--
--   Previous: [`contDiff_posteriorExpectation_joint`](https://prove2.me/theorems/26f7270c-a7c7-4be5-ace6-46911a4ce683) · Next: [`contDiff_covariance_pair_joint`](https://prove2.me/theorems/f0d416e4-4daa-49f4-9fdf-85bc15992dcb).
--
--   [Source excerpt, lines 225–227](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/JointRegularity.lean#L225-L227) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/JointRegularity.lean#L223-L245 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.JointRegularity`, declaration `FunctionalInequalities.Probability.Posterior.contDiff_posteriorMean_joint`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_JointRegularity

open MeasureTheory ProbabilityTheory FunctionalInequalities
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.contDiff_posteriorMean_joint_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => posteriorMean μ p.1 p.2) := by sorry
