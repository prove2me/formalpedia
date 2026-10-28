-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_iSup_dyadicRunMax_drift_le_readable
-- name    : LevyStochCalc.Ito.Picard.iSup_dyadicRunMax_drift_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:42.607586+00:00
-- url     : https://prove2.me/theorems/97da484f-4fa0-43bd-b65b-1daac09db530
-- title:
--   Dyadic Maximum Bound for the Picard Drift
-- statement:
--   This bounds the dyadic running maxima of the drift component by its initial value and total variation.
--
--   Let $\mathrm{coeffs}$ be jump-diffusion coefficients, let $X$ be a state process, let $x_0\in\mathbb R^n$, and fix a coordinate $i<n$. Assume $T'\ge0$ and that
--   $s\mapsto\mu(s,X_s(\omega),i)$ is integrable on $[0,T']$. Then, for every $\omega$,
--
--   $$\sup_m\left\|\operatorname{dyadicRunMax}\bigl(t\mapsto x_{0,i}+\int_0^t\mu(s,X_s(\omega),i)\,ds,T',m\bigr)\right\|$$
--   $$\le |x_{0,i}|+\left|\int_0^{T'}\|\mu(s,X_s(\omega),i)\|\,ds\right|.$$
--
--   The displayed quantities are represented as `ENNReal` coercions of nonnegative norms. This is a pathwise auxiliary estimate for the drift part of the Picard step.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem iSup_dyadicRunMax_drift_le
--       (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
--       (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n) {T' : ℝ} (hT' : 0 ≤ T') {ω : Ω}
--       (hint : MeasureTheory.IntegrableOn (fun s => coeffs.μ s (X s ω) i)
--         (Set.Icc (0 : ℝ) T') volume) :
--       (⨆ m, (‖dyadicRunMax (fun t ω => picardStep_drift coeffs X x₀ t ω i) T' m ω‖₊ : ℝ≥0∞))
--         ≤ (‖x₀ i‖₊ : ℝ≥0∞)
--           + (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardSupL2`](https://prove2.me/theorems/95956ab0-48db-4ddd-b1af-58707e5784c0).
--
--   Definition modules: [`LevyStochCalc/Ito/PicardBieleckiNorm`](https://prove2.me/theorems/7e1224ac-a352-46d7-9a7e-a9c4b7a20a02), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Probability/DoobContinuous`](https://prove2.me/theorems/948ff195-c1ab-45a5-b573-556d15dca780).
--
--   Supporting theorems: [`enorm_dyadicRunMax`](https://prove2.me/theorems/df28b675-5880-4511-8fdc-de21a750c0cb).
--
--   Next: [`lintegral_sq_drift_bound_lt_top`](https://prove2.me/theorems/db81078a-b990-4c25-b393-aaade629f920).
--
--   [Source excerpt, lines 59–66](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardSupL2.lean#L59-L66) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardSupL2.lean#L57-L90 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardSupL2`, declaration `LevyStochCalc.Ito.Picard.iSup_dyadicRunMax_drift_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
omit [MeasurableSpace Ω] [MeasurableSpace E]

theorem LevyStochCalc.Ito.Picard.iSup_dyadicRunMax_drift_le_readable
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n) {T' : ℝ} (hT' : 0 ≤ T') {ω : Ω}
    (hint : MeasureTheory.IntegrableOn (fun s => coeffs.μ s (X s ω) i)
      (Set.Icc (0 : ℝ) T') volume) :
    (⨆ m, (‖dyadicRunMax (fun t ω => picardStep_drift coeffs X x₀ t ω i) T' m ω‖₊ : ℝ≥0∞))
      ≤ (‖x₀ i‖₊ : ℝ≥0∞)
        + (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞) := by sorry
