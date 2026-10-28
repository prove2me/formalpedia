-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_norm_cumulant_le_of_moment_bounds_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.norm_cumulant_le_of_moment_bounds_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:28.004043+00:00
-- url     : https://prove2.me/theorems/2fba5017-7028-4900-bbca-722c2b963872
-- title:
--   Cumulant Norm Bound from Moment Bounds
-- statement:
--   This is a moment-to-cumulant estimate.
--
--   Let $\nu$ be a probability measure on a finite-dimensional real inner-product space $E$. Suppose $r>0$, $e^{r\|x\|}$ is integrable with respect to $\nu$, and for some $m\in\mathbb N$ and $D\in\mathbb R$,
--
--   $$\int\|x\|^i\,d\nu(x)\le D^i\qquad(1\le i\le m).$$
--
--   Then the norm of the $m$-th cumulant tensor satisfies
--
--   $$\|\kappa_m(\nu)\|\le (m!)^2D^m.$$
--
--   This gives a general quantitative bound on cumulants in terms of moments and is independent of any log-concavity assumption.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_cumulant_le_of_moment_bounds
--       {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
--       [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       (ν : Measure E) [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
--       (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) {m : ℕ} {D : ℝ}
--       (hD : ∀ i : ℕ, 1 ≤ i → i ≤ m → (∫ x, ‖x‖ ^ i ∂ν) ≤ D ^ i) :
--       ‖cumulant ν m‖ ≤ (m.factorial : ℝ) ^ 2 * D ^ m
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/MomentBound`](https://prove2.me/theorems/e88bd87c-526f-4996-81d3-77b0500b42c8).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   [Source excerpt, lines 17–23](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/MomentBound.lean#L17-L23) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/MomentBound.lean#L16-L43 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.MomentBound`, declaration `FunctionalInequalities.Analysis.BakryEmery.norm_cumulant_le_of_moment_bounds`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_MomentBound

open MeasureTheory

theorem FunctionalInequalities.Analysis.BakryEmery.norm_cumulant_le_of_moment_bounds_readable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) {m : ℕ} {D : ℝ}
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ m → (∫ x, ‖x‖ ^ i ∂ν) ≤ D ^ i) :
    ‖cumulant ν m‖ ≤ (m.factorial : ℝ) ^ 2 * D ^ m := by sorry
