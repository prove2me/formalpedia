-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sq_polarQuadVarIncrement_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_sq_polarQuadVarIncrement_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:37.644003+00:00
-- url     : https://prove2.me/theorems/3e500a78-fa1d-4509-8fce-e931788339ed
-- title:
--   Second-Moment Bound for Polarized Increments
-- statement:
--   Under the measurability, progressive-measurability, joint square-integrability, and bounds $C\ge0$, $|H_1|\le C$, and $|H_2|\le C$, assume also the required hypotheses for $H_1+H_2$. For $0\le a<b$, the squared polarized compensated increment is integrable and
--
--   $$\int \mathrm{polarQuadVarIncrement}_{a,b}(H_1,H_2)^2\,dP
--   \le 3\bigl(2(6+\gamma_4)+2\bigr)(2C)^4(b-a)^2.$$
--
--   The conclusion includes both integrability and the displayed upper bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_sq_polarQuadVarIncrement_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
--       Integrable (fun ω =>
--           (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2) P
--         ∧ ∫ ω, (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2 ∂P
--           ≤ 3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4) * (b - a) ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/PolarisedQuadVar`](https://prove2.me/theorems/00553e93-f879-4904-9333-b2c00471b79f).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Selected supporting theorems: [`compensator_add_sq_eq`](https://prove2.me/theorems/89a9fb44-6d50-4dd1-8c08-30019bcfbb53), [`compensator_sub_bounds`](https://prove2.me/theorems/5e8ee404-c1c1-469d-8d85-45ab11b64d10), [`integral_sq_quadVarIncrement_le`](https://prove2.me/theorems/bb94fb53-5983-4031-9e2b-578cca0d2b19), [`memLp_two_polarQuadVarIncrement`](https://prove2.me/theorems/e1f3d644-9e95-4545-bc1a-84c062eb6f44), [`memLp_two_sq_increment`](https://prove2.me/theorems/bdf6946b-1242-4316-90ea-7306d70caa0e).
--
--   Previous: [`stronglyMeasurable_polarQuadVarIncrement`](https://prove2.me/theorems/257fc5bd-0d48-42b0-a71b-4fcd26b462bd) · Next: [`integral_sq_weighted_polarQuadVarSum_le`](https://prove2.me/theorems/194ed6f8-bb43-4c00-b88b-c7080958b1e9).
--
--   [Source excerpt, lines 230–234](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/PolarisedQuadVar.lean#L230-L234) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/PolarisedQuadVar.lean#L228-L311 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.PolarisedQuadVar`, declaration `LevyStochCalc.Brownian.Ito.integral_sq_polarQuadVarIncrement_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_PolarisedQuadVar

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/PolarisedQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H₁ H₂ : Ω → ℝ → ℝ)
  (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
  (hp₁ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₁)
  (hp₂ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₂)
  (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
  (hpa : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
  (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
variable {C : ℝ} (hC0 : 0 ≤ C) (hCH₁ : ∀ ω s, |H₁ ω s| ≤ C) (hCH₂ : ∀ ω s, |H₂ ω s| ≤ C)
include hℱ hma hpa hqa hC0 hCH₁ hCH₂

theorem LevyStochCalc.Brownian.Ito.integral_sq_polarQuadVarIncrement_le_readable {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Integrable (fun ω =>
        (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2) P
      ∧ ∫ ω, (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2 ∂P
        ≤ 3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4) * (b - a) ^ 2 := by sorry
