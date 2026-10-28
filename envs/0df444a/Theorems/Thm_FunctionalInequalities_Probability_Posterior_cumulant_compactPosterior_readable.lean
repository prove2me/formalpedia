-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_cumulant_compactPosterior_readable
-- name    : FunctionalInequalities.Probability.Posterior.cumulant_compactPosterior_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:41.08463+00:00
-- url     : https://prove2.me/theorems/be65aff1-f18a-49ae-a8b8-b2bf0b7da5d2
-- title:
--   Posterior Cumulants as Log-Partition Derivatives
-- statement:
--   This formalizes the derivative representation of posterior cumulants used in Lemma 4.3 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), cited there for cumulant dynamics.
--
--   Let $E$ be a complete finite-dimensional real inner-product space, let $\mu$ be a compactly supported probability law, let $c\in E$, let $Q:E\to E$ be continuous linear, and let $m\ge1$. Then the $m$th cumulant tensor of the compact posterior equals the $m$th iterated derivative in the linear parameter $c$ of the log-partition function:
--
--   $$
--   \kappa_m(\mu_{c,Q})
--   = D_c^m\bigl[y\mapsto\psi(y,Q)\bigr](c).
--   $$
--
--   In Lean, the derivative is `iteratedFDeriv ℝ m` and the cumulant is `Analysis.BakryEmery.cumulant`. This identity is the deterministic bridge between posterior cumulants and smooth parameter calculus.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cumulant_compactPosterior (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) {m : ℕ} (hm : 1 ≤ m) :
--       Analysis.BakryEmery.cumulant (compactPosterior μ hc c Q : Measure E) m =
--         iteratedFDeriv ℝ m (fun y => logPartition μ y Q) c
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/LogPartition`](https://prove2.me/theorems/b716da65-348c-498f-97a9-23cbe395f8fd).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda).
--
--   Supporting theorems: [`contDiff_logPartition_joint`](https://prove2.me/theorems/4f6af24d-bf34-47a4-ab0b-b8f6855e12d6), [`logLaplace_compactPosterior`](https://prove2.me/theorems/d8a2d036-0686-4a74-b74b-f00a4e04d654).
--
--   Previous: [`logLaplace_compactPosterior`](https://prove2.me/theorems/d8a2d036-0686-4a74-b74b-f00a4e04d654) · Next: [`fderiv_logPartition_c_apply`](https://prove2.me/theorems/d56dc845-a2d9-42d9-b22a-bbd6ef8df04f).
--
--   [Source excerpt, lines 241–244](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean#L241-L244) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 4.3, p. 20. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean#L240-L303 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.LogPartition`, declaration `FunctionalInequalities.Probability.Posterior.cumulant_compactPosterior`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition

open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.cumulant_compactPosterior_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) {m : ℕ} (hm : 1 ≤ m) :
    Analysis.BakryEmery.cumulant (compactPosterior μ hc c Q : Measure E) m =
      iteratedFDeriv ℝ m (fun y => logPartition μ y Q) c := by sorry
