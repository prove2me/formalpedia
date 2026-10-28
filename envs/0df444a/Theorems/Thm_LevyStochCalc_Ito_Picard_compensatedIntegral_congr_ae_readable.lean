-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_compensatedIntegral_congr_ae_readable
-- name    : LevyStochCalc.Ito.Picard.compensatedIntegral_congr_ae_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:07.229273+00:00
-- url     : https://prove2.me/theorems/4e52f913-b0fa-453d-a760-85ac36d0bb61
-- title:
--   Almost-Everywhere Congruence Of Compensated Poisson Integrals
-- statement:
--   This is an auxiliary locality theorem for compensated Poisson integration. Let $(\Omega,P)$ be a probability space, let $E$ carry a sigma-finite measure $\nu$, let $N$ be a Poisson random measure with filtration $\mathcal F$, and let $\varphi_1,\varphi_2:\Omega\times\mathbb R\times E\to\mathbb R$ be jointly measurable and marked-progressively measurable. Assume that for every $T>0$ their squared integrals are finite:
--
--   $$\int_\Omega\int_{[0,T]}\int_E\|\varphi_r(\omega,s,e)\|_+^2\,d\nu(e)\,ds\,dP<\infty\qquad(r=1,2).$$
--
--   If $t>0$ and $\varphi_1(\omega,s,\cdot)=\varphi_2(\omega,s,\cdot)$ for $P$-almost every $\omega$ and volume-almost every $s\in[0,t]$, then
--
--   $$\int_{[0,t]\times E}\varphi_1\,\widetilde N=\int_{[0,t]\times E}\varphi_2\,\widetilde N\quad\text{almost surely}.$$
--
--   The statement formalizes the time-locality of the compensated-Poisson integral.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem compensatedIntegral_congr_ae {ν : Measure E} [SigmaFinite ν]
--       (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
--       (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
--       (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
--       (φ₁ φ₂ : Ω → ℝ → E → ℝ)
--       (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
--       (hp₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
--       (hs₁ : ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
--       (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
--       (hp₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
--       (hs₂ : ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
--       {t : ℝ} (ht : 0 < t)
--       (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), φ₁ ω s = φ₂ ω s) :
--       ∀ᵐ ω ∂P,
--         LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
--           = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardLocality`](https://prove2.me/theorems/6f022361-7332-41fe-a646-6e283b2f482e).
--
--   Definition modules: [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Poisson/Compensated`](https://prove2.me/theorems/cafbfbf8-33d8-4018-b6c5-9924b126eba7), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Previous: [`itoIntegral_congr_ae`](https://prove2.me/theorems/5b2a8fe4-013f-4df7-9936-5da724b67c11) · Next: [`picardStep_diffusion_congr_ae`](https://prove2.me/theorems/6c336559-f093-4ef9-8ae4-892731263519).
--
--   [Source excerpt, lines 127–144](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardLocality.lean#L127-L144) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardLocality.lean#L126-L163 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardLocality`, declaration `LevyStochCalc.Ito.Picard.compensatedIntegral_congr_ae`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Ito.Picard.compensatedIntegral_congr_ae_readable {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ₁ φ₂ : Ω → ℝ → E → ℝ)
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hp₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (hs₁ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hp₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (hs₂ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), φ₁ ω s = φ₂ ω s) :
    ∀ᵐ ω ∂P,
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
        = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω := by sorry
