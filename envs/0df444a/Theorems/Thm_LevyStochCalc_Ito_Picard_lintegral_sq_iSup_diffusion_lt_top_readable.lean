-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_iSup_diffusion_lt_top_readable
-- name    : LevyStochCalc.Ito.Picard.lintegral_sq_iSup_diffusion_lt_top_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:07.197165+00:00
-- url     : https://prove2.me/theorems/bf146c9c-9e76-4873-bd21-1130aac77e2a
-- title:
--   Finite Dyadic $S^2$ Bound for the Diffusion Component
-- statement:
--   This proves finiteness of the dyadic supremum second moment of one Brownian diffusion coordinate in the Picard step.
--
--   Let $W$ be a $d$-dimensional Brownian motion with filtration $\mathcal F$, let $X$ be a state process, and fix $i<n$. Assume each diffusion coefficient $\sigma_{ij}$ is measurable and progressively measurable, and for every $j<d$ and every $T>0$,
--
--   $$\int_\Omega\int_0^T\|\sigma_{ij}(s,X_s(\omega))\|^2\,ds\,dP(\omega)<\top.$$
--
--   Then for every $T'>0$,
--
--   $$\int_\Omega\left(\sup_m\left\|\operatorname{dyadicRunMax}(\text{diffusion}_i,T',m)(\omega)\right\|\right)^2dP(\omega)<\top.$$
--
--   This is an `ENNReal` finiteness result used in the componentwise $S^2$ estimate.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_sq_iSup_diffusion_lt_top
--       (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
--       (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
--       (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
--       (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
--       (X : ℝ → Ω → (Fin n → ℝ))
--       (h_meas : ∀ i : Fin n, ∀ j : Fin d,
--         Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
--       (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
--         Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
--       (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--           (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
--       ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω =>
--           picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i)
--           T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardSupL2`](https://prove2.me/theorems/95956ab0-48db-4ddd-b1af-58707e5784c0).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Ito/PicardStepMap`](https://prove2.me/theorems/21926b6e-8177-414a-981c-1a2486aea5bd), [`LevyStochCalc/Probability/DoobContinuous`](https://prove2.me/theorems/948ff195-c1ab-45a5-b573-556d15dca780).
--
--   Supporting theorems: [`enorm_dyadicRunMax`](https://prove2.me/theorems/df28b675-5880-4511-8fdc-de21a750c0cb), [`lintegral_sq_dyadicRunMax_le`](https://prove2.me/theorems/c1b80434-c26c-49be-a883-841d52382ee6), [`sq_sum_le_card_sq_mul`](https://prove2.me/theorems/7c556d30-1476-4749-9b82-7ef598da576d).
--
--   Previous: [`lintegral_sq_drift_bound_lt_top`](https://prove2.me/theorems/db81078a-b990-4c25-b393-aaade629f920) · Next: [`lintegral_sq_iSup_picardStep_lt_top`](https://prove2.me/theorems/d29e9d50-932e-426b-8307-33a15070eb09).
--
--   [Source excerpt, lines 205–221](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardSupL2.lean#L205-L221) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardSupL2.lean#L203-L251 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardSupL2`, declaration `LevyStochCalc.Ito.Picard.lintegral_sq_iSup_diffusion_lt_top`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
omit [MeasurableSpace E]

theorem LevyStochCalc.Ito.Picard.lintegral_sq_iSup_diffusion_lt_top_readable
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω =>
        picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i)
        T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by sorry
