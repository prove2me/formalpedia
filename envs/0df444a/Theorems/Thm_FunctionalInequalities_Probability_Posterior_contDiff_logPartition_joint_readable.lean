-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_logPartition_joint_readable
-- name    : FunctionalInequalities.Probability.Posterior.contDiff_logPartition_joint_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:36.551624+00:00
-- url     : https://prove2.me/theorems/4f6af24d-bf34-47a4-ab0b-b8f6855e12d6
-- title:
--   Smoothness of the Joint Log-Partition Function
-- statement:
--   This statement establishes the joint smoothness of the posterior log-partition function described in Section 4 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a complete finite-dimensional real inner-product space with its Borel measurable structure. If $\mu$ is a probability law on $E$ whose support is compact, then the function
--
--   $$
--   (c,Q)\longmapsto \psi(c,Q)
--   =\log\int_E\exp\!\left(\langle c,x\rangle-\frac12\langle Qx,x\rangle\right)\,d\mu(x)
--   $$
--
--   is $C^\infty$ on $E\times(E\to E)$:
--
--   $$
--   \operatorname{ContDiff}(\mathbb{R},\infty,\psi).
--   $$
--
--   The result provides the regularity needed for differentiating posterior cumulants and generator expressions with respect to both posterior parameters.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiff_logPartition_joint
--       [CompleteSpace E] [FiniteDimensional ℝ E]
--       [MeasurableSpace E] [BorelSpace E]
--       (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) :
--       ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => logPartition μ p.1 p.2)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/LogPartition`](https://prove2.me/theorems/b716da65-348c-498f-97a9-23cbe395f8fd).
--
--   Next: [`logLaplace_compactPosterior`](https://prove2.me/theorems/d8a2d036-0686-4a74-b74b-f00a4e04d654).
--
--   [Source excerpt, lines 134–139](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean#L134-L139) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean#L131-L202 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.LogPartition`, declaration `FunctionalInequalities.Probability.Posterior.contDiff_logPartition_joint`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.contDiff_logPartition_joint_readable
    [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => logPartition μ p.1 p.2) := by sorry
