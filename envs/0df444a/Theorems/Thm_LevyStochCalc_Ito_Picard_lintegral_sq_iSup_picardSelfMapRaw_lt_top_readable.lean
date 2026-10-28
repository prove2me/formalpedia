-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_iSup_picardSelfMapRaw_lt_top_readable
-- name    : LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardSelfMapRaw_lt_top_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:02.642976+00:00
-- url     : https://prove2.me/theorems/41b19c73-2054-4724-85c9-087eb1b0c354
-- title:
--   Finite Window $S^2$ Norm of the Raw Picard Self-Map
-- statement:
--   This proves that the raw Picard self-map has finite windowwise $S^2$ norm.
--
--   Let $P$ be a probability measure, $W$ and $N$ be compatible Brownian and Poisson drivers, and let $\mathcal F$ be right-continuous with the stated null-set and pre-zero assumptions. Let the coefficients be regular and Lipschitz. Let $Z$ be measurable and progressively measurable coordinatewise, with finite Bielecki norm on a window $[0,T]$, where $T>0$. For any $T'>0$,
--
--   $$\int_\Omega\sup_{0\le t\le T'}\sum_{i<n}\left\|\bigl(\operatorname{picardSelfMapRaw}(Z)\bigr).X_t(\omega,i)\right\|^2dP(\omega)<\top.$$
--
--   The integral and supremum are represented in `ENNReal`. This supplies the $S^2$ control needed for subsequent fixed-point arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_sq_iSup_picardSelfMapRaw_lt_top
--       (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
--       (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
--       (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
--       (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
--       (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
--       (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
--       (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
--       (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
--       (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
--       {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
--       (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
--       {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
--       (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
--       (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) {T' : ℝ} (hT' : 0 < T') :
--       ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i,
--           (‖(picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb).X
--             (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardSupL2`](https://prove2.me/theorems/95956ab0-48db-4ddd-b1af-58707e5784c0).
--
--   Definition modules: [`LevyStochCalc/Ito/PicardBieleckiNorm`](https://prove2.me/theorems/7e1224ac-a352-46d7-9a7e-a9c4b7a20a02), [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Ito/PicardOutputModification`](https://prove2.me/theorems/f2aa199f-3961-4748-8e22-7d7db164e159), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`lintegral_sq_iSup_picardStep_lt_top`](https://prove2.me/theorems/d29e9d50-932e-426b-8307-33a15070eb09), [`measurable_picardStepOnRawStop_slice`](https://prove2.me/theorems/b756fd53-bc8d-4424-9fc0-745ef08f7652), [`picardSelfMapRaw_ae_eq`](https://prove2.me/theorems/9b049339-6c9f-4000-b846-f53555774ea7), [`enorm_dyadicRunMax`](https://prove2.me/theorems/df28b675-5880-4511-8fdc-de21a750c0cb), [`iSup_enorm_eq_iSup_dyadicRunMax`](https://prove2.me/theorems/acb0a4f1-b242-45cd-80de-139b129bb826).
--
--   Previous: [`lintegral_sq_iSup_picardStep_lt_top`](https://prove2.me/theorems/d29e9d50-932e-426b-8307-33a15070eb09).
--
--   [Source excerpt, lines 334–351](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardSupL2.lean#L334-L351) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardSupL2.lean#L333-L401 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardSupL2`, declaration `LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardSelfMapRaw_lt_top`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardSelfMapRaw_lt_top_readable
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i,
        (‖(picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb).X
          (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by sorry
