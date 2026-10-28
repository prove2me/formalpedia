-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_integral_add_mul_increment_sq_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.integral_add_mul_increment_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:51.772808+00:00
-- url     : https://prove2.me/theorems/d77376ee-50f5-4d6a-b971-007d80feac97
-- title:
--   Second-Moment Expansion for a Brownian Increment
-- statement:
--   This technical lemma gives the second-moment recursion for adding a bounded, time-$a$-measurable multiple of a Brownian increment.
--
--   Let $W$ be a Brownian motion with Brownian filtration $\mathcal F$, let $0\le a<b$, and let $S,\xi:\Omega\to\mathbb R$ satisfy the stated $L^2$, measurability, and $\mathcal F_a$-strong measurability assumptions. Assume $C\ge0$ and $|\xi(\omega)|\le C$ for all $\omega$. Then
--
--   $$
--   \int (S+\xi(W_b-W_a))^2\,dP
--   =\int S^2\,dP+(b-a)\int \xi^2\,dP.
--   $$
--
--   This is an auxiliary identity used in the second-moment recursion for elementary stochastic integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito.SimplePredictable`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem integral_add_mul_increment_sq
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
--       {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {S ξ : Ω → ℝ}
--       (hS2 : MemLp S 2 P) (hSm : Measurable S)
--       (hSad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) S)
--       (hξm : Measurable ξ) (hξad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) ξ)
--       {C : ℝ} (hC0 : 0 ≤ C) (hCξ : ∀ ω, |ξ ω| ≤ C) :
--       ∫ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 2 ∂P
--         = (∫ ω, S ω ^ 2 ∂P) + (∫ ω, ξ ω ^ 2 ∂P) * (b - a)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFourthMomentPartialSums`](https://prove2.me/theorems/705e75c1-4971-40ae-82c1-068282421322).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Supporting theorems: [`integral_mul_increment_pow`](https://prove2.me/theorems/8fc1f6bc-eb0f-42e8-a4c1-562b4c26ab81), [`integral_pow_gaussianReal_zero`](https://prove2.me/theorems/5bcebbba-553a-4972-8595-83ab7dcceb2b).
--
--   Next: [`integral_add_mul_increment_pow_four`](https://prove2.me/theorems/70cfa191-ba5b-406e-9b47-0bc6e678c599).
--
--   [Source excerpt, lines 45–53](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean#L45-L53) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean#L44-L104 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFourthMomentPartialSums`, declaration `_private.LevyStochCalc.Brownian.ItoFourthMomentPartialSums.0.LevyStochCalc.Brownian.Ito.SimplePredictable.integral_add_mul_increment_sq`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.integral_add_mul_increment_sq_readable
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {S ξ : Ω → ℝ}
    (hS2 : MemLp S 2 P) (hSm : Measurable S)
    (hSad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) S)
    (hξm : Measurable ξ) (hξad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) ξ)
    {C : ℝ} (hC0 : 0 ≤ C) (hCξ : ∀ ω, |ξ ω| ≤ C) :
    ∫ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 2 ∂P
      = (∫ ω, S ω ^ 2 ∂P) + (∫ ω, ξ ω ^ 2 ∂P) * (b - a) := by sorry
