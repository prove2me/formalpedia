-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_factor_increment_sq_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_factor_increment_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:15.718769+00:00
-- url     : https://prove2.me/theorems/a261136e-59cf-42dc-be13-44c2ab2acb19
-- title:
--   Weighted Brownian Increment Second Moment
-- statement:
--   This states a weighted second-moment identity for a Brownian motion $W$ under a probability measure $P$ and a Brownian filtration $\mathcal F$. Let $0\le a<b$, and let $g:\Omega\to\mathbb R$ be strongly measurable with respect to $\mathcal F_a$. Then
--
--   $$\int_\Omega g(\omega)\bigl(W_b(\omega)-W_a(\omega)\bigr)^2\,dP(\omega)
--   =\left(\int_\Omega g\,dP\right)(b-a).$$
--
--   The result records the conditional diagonal calculation for an increment square; its stated assumptions include only strong $\mathcal F_a$-measurability of $g$, besides the probability and Brownian-filtration hypotheses.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma integral_factor_increment_sq
--       {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
--       (W : LevyStochCalc.Brownian.BrownianMotion P)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a)
--         (hab : a < b)
--       {g : Ω → ℝ}
--       (hg_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ a) g) :
--       ∫ ω, g ω * (W.W b ω - W.W a ω) ^ 2 ∂P = (∫ ω, g ω ∂P) * (b - a)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoL2CompletionConvergence`](https://prove2.me/theorems/7052eb64-0ceb-40e0-81f7-f59b0f13c887).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Previous: [`condExp_sq_increment_of_martingale`](https://prove2.me/theorems/9248f0a4-cf9c-4337-bd6c-ca5656254c6a).
--
--   [Source excerpt, lines 540–548](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean#L540-L548) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean#L537-L566 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionConvergence`, declaration `LevyStochCalc.Brownian.Ito.integral_factor_increment_sq`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionConvergence

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma LevyStochCalc.Brownian.Ito.integral_factor_increment_sq_readable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a)
      (hab : a < b)
    {g : Ω → ℝ}
    (hg_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g) :
    ∫ ω, g ω * (W.W b ω - W.W a ω) ^ 2 ∂P = (∫ ω, g ω ∂P) * (b - a) := by sorry
