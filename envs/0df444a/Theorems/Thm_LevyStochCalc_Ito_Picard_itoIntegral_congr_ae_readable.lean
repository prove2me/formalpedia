-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_itoIntegral_congr_ae_readable
-- name    : LevyStochCalc.Ito.Picard.itoIntegral_congr_ae_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:24.182617+00:00
-- url     : https://prove2.me/theorems/5b2a8fe4-013f-4df7-9936-5da724b67c11
-- title:
--   Almost-Everywhere Congruence Of Itô Integrals
-- statement:
--   This is an auxiliary locality theorem for the Brownian Itô integral. Let $W_j$ be a Brownian motion on a probability space $(\Omega,P)$ with Brownian filtration $\mathcal F$. Let $H_1,H_2:\Omega\times\mathbb R\to\mathbb R$ be jointly measurable and progressively measurable, and assume that for every $T>0$ their squared $\operatorname{ENNReal}$ norms are integrable over $\Omega\times[0,T]$:
--
--   $$\int_\Omega\int_{[0,T]}\|H_r(\omega,s)\|_+^2\,ds\,dP<\infty\qquad(r=1,2).$$
--
--   If $t>0$ and $H_1(\omega,s)=H_2(\omega,s)$ for $P$-almost every $\omega$ and volume-almost every $s\in[0,t]$, then
--
--   $$\int_0^t H_1\,dW_j=\int_0^t H_2\,dW_j\quad\text{for }P\text{-almost every }\omega.$$
--
--   The lemma records that the stochastic integral at time $t$ depends only on the integrand up to product-null equality on $[0,t]$.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem itoIntegral_congr_ae
--       (Wj : LevyStochCalc.Brownian.BrownianMotion P)
--       (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
--       (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration Wj ℱ)
--       (H₁ H₂ : Ω → ℝ → ℝ)
--       (hm₁ : Measurable (Function.uncurry H₁))
--       (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
--       (hs₁ : ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hm₂ : Measurable (Function.uncurry H₂))
--       (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
--       (hs₂ : ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {t : ℝ} (ht : 0 < t)
--       (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), H₁ ω s = H₂ ω s) :
--       ∀ᵐ ω ∂P, LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
--         = LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardLocality`](https://prove2.me/theorems/6f022361-7332-41fe-a646-6e283b2f482e).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionApi`](https://prove2.me/theorems/2726bba3-f240-429d-9052-e494c979e1f0), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Next: [`compensatedIntegral_congr_ae`](https://prove2.me/theorems/4e52f913-b0fa-453d-a760-85ac36d0bb61).
--
--   [Source excerpt, lines 90–106](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardLocality.lean#L90-L106) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardLocality.lean#L89-L124 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardLocality`, declaration `LevyStochCalc.Ito.Picard.itoIntegral_congr_ae`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardLocality

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}

theorem LevyStochCalc.Ito.Picard.itoIntegral_congr_ae_readable
    (Wj : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration Wj ℱ)
    (H₁ H₂ : Ω → ℝ → ℝ)
    (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hs₁ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hs₂ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), H₁ ω s = H₂ ω s) :
    ∀ᵐ ω ∂P, LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
      = LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω := by sorry
