-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_logLaplace_compactPosterior_readable
-- name    : FunctionalInequalities.Probability.Posterior.logLaplace_compactPosterior_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:33.486707+00:00
-- url     : https://prove2.me/theorems/d8a2d036-0686-4a74-b74b-f00a4e04d654
-- title:
--   Log-Laplace Formula for Compact Posteriors
-- statement:
--   This statement gives the log-Laplace identity for a compactly supported linear–quadratic posterior.
--
--   Let $E$ be a complete finite-dimensional real inner-product space, let $\mu$ be a probability law with compact support, let $c,z\in E$, and let $Q:E\to E$ be continuous linear. For the compact posterior $\mu_{c,Q}$ and the log-partition function $\psi=\texttt{logPartition}\,\mu$, one has
--
--   $$
--   \Lambda_{\mu_{c,Q}}(z)
--   =\psi(c+z,Q)-\psi(c,Q),
--   $$
--
--   where $\Lambda$ is `Analysis.BakryEmery.logLaplace`. The identity is a direct formula for the posterior log-Laplace transform and is reusable in derivative and cumulant calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   omit [CompleteSpace E] [FiniteDimensional ℝ E]
--     [MeasurableSpace E] [BorelSpace E] in
--   theorem logLaplace_compactPosterior
--       [CompleteSpace E] [FiniteDimensional ℝ E]
--       [MeasurableSpace E] [BorelSpace E]
--       (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (z : E) :
--       Analysis.BakryEmery.logLaplace (compactPosterior μ hc c Q : Measure E) z =
--         logPartition μ (c + z) Q - logPartition μ c Q
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/LogPartition`](https://prove2.me/theorems/b716da65-348c-498f-97a9-23cbe395f8fd).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda).
--
--   Previous: [`contDiff_logPartition_joint`](https://prove2.me/theorems/4f6af24d-bf34-47a4-ab0b-b8f6855e12d6) · Next: [`cumulant_compactPosterior`](https://prove2.me/theorems/be65aff1-f18a-49ae-a8b8-b2bf0b7da5d2).
--
--   [Source excerpt, lines 204–212](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean#L204-L212) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean#L204-L238 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.LogPartition`, declaration `FunctionalInequalities.Probability.Posterior.logLaplace_compactPosterior`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition

open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.logLaplace_compactPosterior_readable
    [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (z : E) :
    Analysis.BakryEmery.logLaplace (compactPosterior μ hc c Q : Measure E) z =
      logPartition μ (c + z) Q - logPartition μ c Q := by sorry
