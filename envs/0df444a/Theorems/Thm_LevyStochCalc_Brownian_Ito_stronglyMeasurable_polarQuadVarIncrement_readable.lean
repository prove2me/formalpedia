-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stronglyMeasurable_polarQuadVarIncrement_readable
-- name    : LevyStochCalc.Brownian.Ito.stronglyMeasurable_polarQuadVarIncrement_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:54.989552+00:00
-- url     : https://prove2.me/theorems/257fc5bd-0d48-42b0-a71b-4fcd26b462bd
-- title:
--   Endpoint Measurability of Polarized Increments
-- statement:
--   Let $H_1,H_2$ satisfy the stated measurability, progressive-measurability, and joint square-integrability assumptions. For any $a\le b$, the function
--
--   $$\omega\longmapsto\mathrm{polarQuadVarIncrement}_{a,b}(H_1,H_2)(\omega)$$
--
--   is strongly measurable with respect to the right-continuous sigma-algebra $\mathcal F.\mathrm{rightCont}_b$. No positivity or boundedness assumption on the integrands is required in this measurability statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stronglyMeasurable_polarQuadVarIncrement {a b : ℝ} (hab : a ≤ b) :
--       @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
--         (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/PolarisedQuadVar`](https://prove2.me/theorems/00553e93-f879-4904-9333-b2c00471b79f).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Previous: [`condExp_polarQuadVarIncrement`](https://prove2.me/theorems/90ba8838-f516-4c4a-a54e-03f7270ecbb4) · Next: [`integral_sq_polarQuadVarIncrement_le`](https://prove2.me/theorems/3e500a78-fa1d-4509-8fce-e931788339ed).
--
--   [Source excerpt, lines 209–211](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/PolarisedQuadVar.lean#L209-L211) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/PolarisedQuadVar.lean#L206-L226 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.PolarisedQuadVar`, declaration `LevyStochCalc.Brownian.Ito.stronglyMeasurable_polarQuadVarIncrement`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_PolarisedQuadVar

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/PolarisedQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
include hℱ

theorem LevyStochCalc.Brownian.Ito.stronglyMeasurable_polarQuadVarIncrement_readable {a b : ℝ} (hab : a ≤ b) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b) := by sorry
