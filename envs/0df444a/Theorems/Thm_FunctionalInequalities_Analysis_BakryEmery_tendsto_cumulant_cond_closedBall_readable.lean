-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tendsto_cumulant_cond_closedBall_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.tendsto_cumulant_cond_closedBall_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:32.798906+00:00
-- url     : https://prove2.me/theorems/5a26c5c6-06d4-47bc-a7e9-de2a1a85735b
-- title:
--   Convergence of Cumulants Under Ball Conditioning
-- statement:
--   This formalizes the cumulant-convergence reduction associated with Theorem 4.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 18.
--
--   Let $E$ be a complete finite-dimensional real inner-product space with its Borel measurable structure, and let $\nu$ be a probability measure on $E$. Assume:
--
--   1. $r>0$.
--   2. $\int e^{r\|x\|}\,d\nu(x)<\infty$.
--   3. $k\in\mathbb N$.
--
--   For the conditional probability measure $\nu[\mid\overline B(0,R)]$ on the closed ball of radius $R$, its $k$th cumulant converges to the $k$th cumulant of $\nu$:
--
--   $$
--   \operatorname{cumulant}\bigl(\nu[\mid\overline B(0,R)]\bigr)_k
--   \longrightarrow
--   \operatorname{cumulant}(\nu)_k
--   \qquad(R\to\infty).
--   $$
--
--   The result is a technical truncation theorem that permits passage from compactly supported conditional laws to the original law in fixed cumulant order.
--
--   **Formalization Note** `cumulant` is a formal multilinear-series object. The conditioning is Lean's `ProbabilityTheory.cond` on `Metric.closedBall (0 : E) R`; the limit parameter is $R\in\mathbb N$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_cumulant_cond_closedBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       (ν : Measure E) [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
--       (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (k : ℕ) :
--       Tendsto (fun R : ℕ => cumulant (ν[|Metric.closedBall (0 : E) R]) k) atTop
--         (𝓝 (cumulant ν k))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Truncation`](https://prove2.me/theorems/1997edb8-3ab3-4dc8-9655-6994bac1ddde).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Supporting theorems: [`cumulant_eq_taylorComp_cond`](https://prove2.me/theorems/e57746d5-e68b-403d-82bc-29f420d708e4), [`tendsto_iteratedFDeriv_laplace_cond_closedBall`](https://prove2.me/theorems/57a5ae82-e2eb-414c-9f9c-2995a3f53149).
--
--   Previous: [`cumulant_eq_taylorComp_cond`](https://prove2.me/theorems/e57746d5-e68b-403d-82bc-29f420d708e4).
--
--   [Source excerpt, lines 215–220](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean#L215-L220) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean#L211-L251 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation`, declaration `FunctionalInequalities.Analysis.BakryEmery.tendsto_cumulant_cond_closedBall`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Truncation

open MeasureTheory ProbabilityTheory Filter Topology

theorem FunctionalInequalities.Analysis.BakryEmery.tendsto_cumulant_cond_closedBall_readable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (k : ℕ) :
    Tendsto (fun R : ℕ => cumulant (ν[|Metric.closedBall (0 : E) R]) k) atTop
      (𝓝 (cumulant ν k)) := by sorry
