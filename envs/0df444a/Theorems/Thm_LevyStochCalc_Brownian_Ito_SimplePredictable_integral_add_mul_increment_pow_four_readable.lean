-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_integral_add_mul_increment_pow_four_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.integral_add_mul_increment_pow_four_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:47.398977+00:00
-- url     : https://prove2.me/theorems/70cfa191-ba5b-406e-9b47-0bc6e678c599
-- title:
--   Fourth-Moment Expansion for a Brownian Increment
-- statement:
--   This technical lemma gives the fourth-moment recursion for adding a bounded, time-$a$-measurable multiple of a Brownian increment.
--
--   Let $W$ be a Brownian motion with Brownian filtration $\mathcal F$, let $0\le a<b$, and let $S,\xi:\Omega\to\mathbb R$ satisfy:
--
--   1. $S\in L^4(P)$ and $S$ is measurable and strongly measurable with respect to $\mathcal F_a$;
--   2. $\xi$ is measurable and strongly measurable with respect to $\mathcal F_a$;
--   3. $C\ge0$ and $|\xi(\omega)|\le C$ for every $\omega$.
--
--   Then
--
--   $$
--   \begin{aligned}
--   \int (S+\xi(W_b-W_a))^4\,dP
--   ={}&\int S^4\,dP
--   +6(b-a)\int S^2\xi^2\,dP\\
--   &+(b-a)^2\,\mathsf g_4\int \xi^4\,dP,
--   \end{aligned}
--   $$
--
--   where $\mathsf g_4$ is `gaussianFourthMoment`. This result is an auxiliary one-step identity for fourth-moment recursions.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito.SimplePredictable`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem integral_add_mul_increment_pow_four
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
--       {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {S ξ : Ω → ℝ}
--       (hS4 : MemLp S 4 P) (hSm : Measurable S)
--       (hSad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) S)
--       (hξm : Measurable ξ) (hξad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) ξ)
--       {C : ℝ} (hC0 : 0 ≤ C) (hCξ : ∀ ω, |ξ ω| ≤ C) :
--       ∫ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 4 ∂P
--         = (∫ ω, S ω ^ 4 ∂P)
--           + 6 * ((∫ ω, S ω ^ 2 * ξ ω ^ 2 ∂P) * (b - a))
--           + (∫ ω, ξ ω ^ 4 ∂P) * ((b - a) ^ 2 * gaussianFourthMoment)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFourthMomentPartialSums`](https://prove2.me/theorems/705e75c1-4971-40ae-82c1-068282421322).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3).
--
--   Supporting theorems: [`integral_mul_increment_pow`](https://prove2.me/theorems/8fc1f6bc-eb0f-42e8-a4c1-562b4c26ab81), [`integral_pow_gaussianReal_zero`](https://prove2.me/theorems/5bcebbba-553a-4972-8595-83ab7dcceb2b).
--
--   Previous: [`integral_add_mul_increment_sq`](https://prove2.me/theorems/d77376ee-50f5-4d6a-b971-007d80feac97) · Next: [`integral_partialSum_sq_succ`](https://prove2.me/theorems/9bf4edcb-e687-4a69-83b1-87842c0ed837).
--
--   [Source excerpt, lines 107–117](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean#L107-L117) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean#L106-L225 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFourthMomentPartialSums`, declaration `_private.LevyStochCalc.Brownian.ItoFourthMomentPartialSums.0.LevyStochCalc.Brownian.Ito.SimplePredictable.integral_add_mul_increment_pow_four`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentPartialSums

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.integral_add_mul_increment_pow_four_readable
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {S ξ : Ω → ℝ}
    (hS4 : MemLp S 4 P) (hSm : Measurable S)
    (hSad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) S)
    (hξm : Measurable ξ) (hξad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) ξ)
    {C : ℝ} (hC0 : 0 ≤ C) (hCξ : ∀ ω, |ξ ω| ≤ C) :
    ∫ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 4 ∂P
      = (∫ ω, S ω ^ 4 ∂P)
        + 6 * ((∫ ω, S ω ^ 2 * ξ ω ^ 2 ∂P) * (b - a))
        + (∫ ω, ξ ω ^ 4 ∂P) * ((b - a) ^ 2 * gaussianFourthMoment) := by sorry
