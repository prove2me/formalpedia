-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_fderiv_logPartition_c_apply_readable
-- name    : FunctionalInequalities.Probability.Posterior.fderiv_logPartition_c_apply_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:13.706741+00:00
-- url     : https://prove2.me/theorems/d56dc845-a2d9-42d9-b22a-bbd6ef8df04f
-- title:
--   Gradient of the Posterior Log-Partition Function
-- statement:
--   This identifies the $c$-gradient of the posterior log-partition function with the posterior mean.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $\mu$ be a compactly supported probability measure on $E$, let $c,h\in E$, and let $Q:E\to E$ be a continuous linear map. For
--
--   $$
--   \psi(c,Q)=\log\int \exp\!\left(\langle c,x\rangle-\tfrac12\langle Qx,x\rangle\right)\,d\mu(x),
--   $$
--
--   one has
--
--   $$
--   D_c\psi(c,Q)[h]=\langle h,\operatorname{posteriorMean}(\mu,c,Q)\rangle.
--   $$
--
--   The formal definitions are `logPartition` and `posteriorMean`. Compact support supplies the differentiability and integrability assumptions required by the statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem fderiv_logPartition_c_apply (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (h : E) :
--       fderiv ℝ (fun y => logPartition μ y Q) c h = ⟪h, posteriorMean μ c Q⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/LogPartition`](https://prove2.me/theorems/b716da65-348c-498f-97a9-23cbe395f8fd).
--
--   Definition modules: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363).
--
--   Supporting theorems: [`contDiff_weighted_integral_quadraticExponent_of_compact`](https://prove2.me/theorems/4fe89257-70b6-4433-b7b3-1b2d874f4eb1), [`exists_uniform_norm_moments_tilted_quadraticExponent_of_compact`](https://prove2.me/theorems/840d9ee9-637c-4b2c-918e-01a3cf6f78a7), [`hasDerivAt_weighted_integral_of_compact`](https://prove2.me/theorems/54d90089-92ce-40ab-9311-3ac0348d33d5).
--
--   Previous: [`cumulant_compactPosterior`](https://prove2.me/theorems/be65aff1-f18a-49ae-a8b8-b2bf0b7da5d2).
--
--   [Source excerpt, lines 306–308](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean#L306-L308) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean#L305-L405 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.LogPartition`, declaration `FunctionalInequalities.Probability.Posterior.fderiv_logPartition_c_apply`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.fderiv_logPartition_c_apply_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (h : E) :
    fderiv ℝ (fun y => logPartition μ y Q) c h = ⟪h, posteriorMean μ c Q⟫ := by sorry
