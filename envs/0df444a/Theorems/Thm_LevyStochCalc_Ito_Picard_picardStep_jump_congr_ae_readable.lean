-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_jump_congr_ae_readable
-- name    : LevyStochCalc.Ito.Picard.picardStep_jump_congr_ae_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:38.236076+00:00
-- url     : https://prove2.me/theorems/dbbc5d31-c9ed-480b-b61a-98ddb19cdde2
-- title:
--   Locality Of The Compensated-Poisson Picard Component
-- statement:
--   This is an auxiliary locality statement for the jump component of the Picard step. Let $N$ be a Poisson random measure with sigma-finite mark measure $\nu$ and filtration $\mathcal F$, let the jump coefficient be $\gamma$, and let $X,Y:\mathbb R\to\Omega\to(\operatorname{Fin}(n)\to\mathbb R)$. Assume the coefficient processes $\gamma(s,X_s,e)_i$ and $\gamma(s,Y_s,e)_i$ are measurable, marked-progressively measurable, and have finite squared integrals over every positive finite time interval. If $t>0$ and $X_s(\omega)=Y_s(\omega)$ for $P$-almost every $\omega$ and volume-almost every $s\in[0,t]$, then
--
--   $$\operatorname{picardStep\_jump}(X,t,\omega)=\operatorname{picardStep\_jump}(Y,t,\omega)$$
--
--   for $P$-almost every $\omega$. This lemma supplies the jump part of the full Picard-step locality result.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem picardStep_jump_congr_ae
--       (h_γ_meas_X : ∀ i : Fin n,
--         Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
--       (h_γ_progMeas_X : ∀ i : Fin n,
--         Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
--       (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
--           (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
--       (h_γ_meas_Y : ∀ i : Fin n,
--         Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i)
--       (h_γ_progMeas_Y : ∀ i : Fin n,
--         Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
--       (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
--           (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
--       {t : ℝ} (ht : 0 < t)
--       (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
--       ∀ᵐ ω ∂P,
--         picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
--           = picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardLocality`](https://prove2.me/theorems/6f022361-7332-41fe-a646-6e283b2f482e).
--
--   Definition modules: [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Ito/PicardStepMap`](https://prove2.me/theorems/21926b6e-8177-414a-981c-1a2486aea5bd), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`compensatedIntegral_congr_ae`](https://prove2.me/theorems/4e52f913-b0fa-453d-a760-85ac36d0bb61).
--
--   Previous: [`picardStep_diffusion_congr_ae`](https://prove2.me/theorems/6c336559-f093-4ef9-8ae4-892731263519).
--
--   [Source excerpt, lines 234–253](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardLocality.lean#L234-L253) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardLocality.lean#L233-L269 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardLocality`, declaration `LevyStochCalc.Ito.Picard.picardStep_jump_congr_ae`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)

theorem LevyStochCalc.Ito.Picard.picardStep_jump_congr_ae_readable
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_X : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_Y : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P,
      picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        = picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω := by sorry
