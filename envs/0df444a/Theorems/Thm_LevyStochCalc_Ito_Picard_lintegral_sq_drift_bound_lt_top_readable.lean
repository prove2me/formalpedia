-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_drift_bound_lt_top_readable
-- name    : LevyStochCalc.Ito.Picard.lintegral_sq_drift_bound_lt_top_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:51.146187+00:00
-- url     : https://prove2.me/theorems/db81078a-b990-4c25-b393-aaade629f920
-- title:
--   Square Integrability of the Drift Dominator
-- statement:
--   This proves that the drift dominator has finite second moment.
--
--   Let $P$ be a probability measure, let $\mathrm{coeffs}$, $X$, $x_0$, and $i<n$ be as above, and let $T'\ge0$. Assume the drift integrand is measurable and
--
--   $$\int_\Omega\int_0^{T'}\|\mu(s,X_s(\omega),i)\|^2\,ds\,dP(\omega)<\top.$$
--
--   Then
--
--   $$\int_\Omega\left(|x_{0,i}|+\left|\int_0^{T'}\|\mu(s,X_s(\omega),i)\|\,ds\right|\right)^2dP(\omega)<\top.$$
--
--   All integrals are `ENNReal` lower integrals and $\top$ denotes infinity. The result supplies the finite drift contribution for an $S^2$ estimate.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_sq_drift_bound_lt_top
--       (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
--       (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n) {T' : ℝ} (hT' : 0 ≤ T')
--       (hμm : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
--       (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
--         (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
--       ∫⁻ ω, ((‖x₀ i‖₊ : ℝ≥0∞)
--           + (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardSupL2`](https://prove2.me/theorems/95956ab0-48db-4ddd-b1af-58707e5784c0).
--
--   Definition modules: [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7).
--
--   Previous: [`iSup_dyadicRunMax_drift_le`](https://prove2.me/theorems/97da484f-4fa0-43bd-b65b-1daac09db530) · Next: [`lintegral_sq_iSup_diffusion_lt_top`](https://prove2.me/theorems/bf146c9c-9e76-4873-bd21-1130aac77e2a).
--
--   [Source excerpt, lines 94–101](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardSupL2.lean#L94-L101) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardSupL2.lean#L92-L118 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardSupL2`, declaration `LevyStochCalc.Ito.Picard.lintegral_sq_drift_bound_lt_top`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Ito.Picard.lintegral_sq_drift_bound_lt_top_readable
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n) {T' : ℝ} (hT' : 0 ≤ T')
    (hμm : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, ((‖x₀ i‖₊ : ℝ≥0∞)
        + (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by sorry
