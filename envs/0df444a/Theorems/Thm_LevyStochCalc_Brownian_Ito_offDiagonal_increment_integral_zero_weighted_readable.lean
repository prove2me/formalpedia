-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_offDiagonal_increment_integral_zero_weighted_readable
-- name    : LevyStochCalc.Brownian.Ito.offDiagonal_increment_integral_zero_weighted_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:25.792979+00:00
-- url     : https://prove2.me/theorems/f2dfb111-9070-47ca-850d-5692b6155761
-- title:
--   Weighted Off-Diagonal Brownian Cancellation
-- statement:
--   This establishes cancellation of a weighted product of separated Brownian increments. Let $W$ be a Brownian motion with Brownian filtration $\mathcal F$, let $0\le a_1<b_1\le a_2<b_2$, and let $\xi_1,\xi_2,g:\Omega\to\mathbb R$ be strongly measurable with respect to $\mathcal F_{a_1}$, $\mathcal F_{a_2}$, and $\mathcal F_{a_1}$, respectively. Then
--
--   $$\int g\,\bigl(\xi_1(W_{b_1}-W_{a_1})\bigr)\bigl(\xi_2(W_{b_2}-W_{a_2})\bigr)\,dP=0.$$
--
--   This is a technical off-diagonal identity used when expanding squared sums of Brownian increments; the later increment is conditionally centered relative to the information available at $a_2$.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma offDiagonal_increment_integral_zero_weighted
--       {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
--       (W : LevyStochCalc.Brownian.BrownianMotion P)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
--       {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (h₁ : a₁ < b₁) (h₁₂ : b₁ ≤ a₂) (h₂ : a₂ < b₂)
--       (ξ₁ ξ₂ g : Ω → ℝ)
--       (hadapt₁ : @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ a₁) ξ₁)
--       (hadapt₂ : @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ a₂) ξ₂)
--       (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ a₁) g) :
--       ∫ ω, g ω * ((ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω))) ∂P
--         = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoL2CompletionCompensator`](https://prove2.me/theorems/11b95172-ce21-4778-ae54-6649149ee1fc).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Next: [`simpleIntegral_sub_eq_clamp_sum`](https://prove2.me/theorems/5b6d9d87-e4ca-4af9-8b0b-701697a48c84).
--
--   [Source excerpt, lines 74–87](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean#L74-L87) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean#L67-L132 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionCompensator`, declaration `LevyStochCalc.Brownian.Ito.offDiagonal_increment_integral_zero_weighted`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionCompensator

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma LevyStochCalc.Brownian.Ito.offDiagonal_increment_integral_zero_weighted_readable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (h₁ : a₁ < b₁) (h₁₂ : b₁ ≤ a₂) (h₂ : a₂ < b₂)
    (ξ₁ ξ₂ g : Ω → ℝ)
    (hadapt₁ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) ξ₁)
    (hadapt₂ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₂)
    (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) g) :
    ∫ ω, g ω * ((ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω))) ∂P
      = 0 := by sorry
