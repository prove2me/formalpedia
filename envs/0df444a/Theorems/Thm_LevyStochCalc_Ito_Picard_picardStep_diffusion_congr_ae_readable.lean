-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_diffusion_congr_ae_readable
-- name    : LevyStochCalc.Ito.Picard.picardStep_diffusion_congr_ae_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:41.769982+00:00
-- url     : https://prove2.me/theorems/6c336559-f093-4ef9-8ae4-892731263519
-- title:
--   Locality Of The Brownian Picard Component
-- statement:
--   This is an auxiliary locality statement for the Brownian component of the Picard step. Let $W$ be a $d$-dimensional Brownian motion with Brownian filtration $\mathcal F$, let the coefficient map $\sigma$ be part of the jump-diffusion coefficients, and let $X,Y:\mathbb R\to\Omega\to(\operatorname{Fin}(n)\to\mathbb R)$. Assume that every coefficient process $\sigma(s,X_s)_{ij}$ and $\sigma(s,Y_s)_{ij}$ is jointly measurable, progressively measurable, and has finite squared $\operatorname{ENNReal}$ integral on every positive finite interval. If $t>0$ and
--
--   $$X_s(\omega)=Y_s(\omega)$$
--
--   for $P$-almost every $\omega$ and volume-almost every $s\in[0,t]$, then the vector-valued diffusion components agree almost surely at $t$:
--
--   $$\operatorname{picardStep\_diffusion}(X,t,\omega)=\operatorname{picardStep\_diffusion}(Y,t,\omega)\quad\text{for }P\text{-almost every }\omega.$$
--
--   The result isolates the Brownian part of the Picard-step locality argument.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem picardStep_diffusion_congr_ae
--       (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
--         Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
--       (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
--         Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
--       (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--           (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
--         Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
--       (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
--         Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
--       (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--           (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {t : ℝ} (ht : 0 < t)
--       (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
--       ∀ᵐ ω ∂P,
--         picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
--           = picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardLocality`](https://prove2.me/theorems/6f022361-7332-41fe-a646-6e283b2f482e).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Ito/PicardStepMap`](https://prove2.me/theorems/21926b6e-8177-414a-981c-1a2486aea5bd).
--
--   Supporting theorems: [`itoIntegral_congr_ae`](https://prove2.me/theorems/5b2a8fe4-013f-4df7-9936-5da724b67c11).
--
--   Previous: [`compensatedIntegral_congr_ae`](https://prove2.me/theorems/4e52f913-b0fa-453d-a760-85ac36d0bb61) · Next: [`picardStep_jump_congr_ae`](https://prove2.me/theorems/dbbc5d31-c9ed-480b-b61a-98ddb19cdde2).
--
--   [Source excerpt, lines 196–215](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardLocality.lean#L196-L215) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardLocality.lean#L194-L231 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardLocality`, declaration `LevyStochCalc.Ito.Picard.picardStep_diffusion_congr_ae`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
omit [MeasurableSpace E]

theorem LevyStochCalc.Ito.Picard.picardStep_diffusion_congr_ae_readable
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P,
      picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
        = picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω := by sorry
