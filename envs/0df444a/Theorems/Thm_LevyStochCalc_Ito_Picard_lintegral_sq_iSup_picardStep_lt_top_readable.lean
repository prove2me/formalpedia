-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_iSup_picardStep_lt_top_readable
-- name    : LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardStep_lt_top_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:03.994539+00:00
-- url     : https://prove2.me/theorems/d29e9d50-932e-426b-8307-33a15070eb09
-- title:
--   Finite Dyadic $S^2$ Bound for the Picard Step
-- statement:
--   This states that each coordinate of the Picard step has finite dyadic $S^2$ norm on every positive window.
--
--   Let $P$ be a probability measure, $W$ a multidimensional Brownian motion, $N$ a Poisson random measure with sigma-finite intensity, and $\mathcal F$ compatible filtrations. Let $\mathrm{coeffs}$ be the jump-diffusion coefficients and $X$ a state process. Assume the diffusion and jump coefficients are measurable, progressively measurable, and have finite squared energies on every positive window; assume also that the drift is measurable and has finite squared energy on every positive window.
--
--   For every coordinate $i<n$ and every $T'>0$,
--
--   $$\int_\Omega\left(\sup_m\left\|\operatorname{dyadicRunMax}(\operatorname{picardStep}_i,T',m)(\omega)\right\|\right)^2dP(\omega)<\top.$$
--
--   The conclusion is an `ENNReal` strict-finiteness statement and is used to show that the Picard step belongs to the required $S^2$ class.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--         Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
--       (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
--           (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
--       (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
--       (hμsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
--           (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
--       ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω =>
--           picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
--             h_γ_meas h_γ_progMeas h_γ_sq t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardSupL2`](https://prove2.me/theorems/95956ab0-48db-4ddd-b1af-58707e5784c0).
--
--   Definition modules: [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Ito/PicardStepMap`](https://prove2.me/theorems/21926b6e-8177-414a-981c-1a2486aea5bd), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Probability/DoobContinuous`](https://prove2.me/theorems/948ff195-c1ab-45a5-b573-556d15dca780).
--
--   Supporting theorems: [`iSup_dyadicRunMax_drift_le`](https://prove2.me/theorems/97da484f-4fa0-43bd-b65b-1daac09db530), [`lintegral_sq_drift_bound_lt_top`](https://prove2.me/theorems/db81078a-b990-4c25-b393-aaade629f920), [`lintegral_sq_iSup_diffusion_lt_top`](https://prove2.me/theorems/bf146c9c-9e76-4873-bd21-1130aac77e2a), [`enorm_dyadicRunMax`](https://prove2.me/theorems/df28b675-5880-4511-8fdc-de21a750c0cb), [`lintegral_sq_dyadicRunMax_le`](https://prove2.me/theorems/c1b80434-c26c-49be-a883-841d52382ee6).
--
--   Previous: [`lintegral_sq_iSup_diffusion_lt_top`](https://prove2.me/theorems/bf146c9c-9e76-4873-bd21-1130aac77e2a) · Next: [`lintegral_sq_iSup_picardSelfMapRaw_lt_top`](https://prove2.me/theorems/41b19c73-2054-4724-85c9-087eb1b0c354).
--
--   [Source excerpt, lines 272–283](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardSupL2.lean#L272-L283) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardSupL2.lean#L253-L329 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardSupL2`, declaration `LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardStep_lt_top`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardSupL2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardSupL2.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]

theorem LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardStep_lt_top_readable
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω =>
        picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
          h_γ_meas h_γ_progMeas h_γ_sq t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by sorry
