-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sq_polarQuadVarIncrement_le
-- name    : LevyStochCalc.Brownian.Ito.integral_sq_polarQuadVarIncrement_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:22:46.097988+00:00
-- url     : https://prove2.me/theorems/7ba7a45b-c033-445c-b13e-2b04ac4be72e
-- title:
--   integral sq polarQuadVarIncrement le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.integral_sq_polarQuadVarIncrement_le` is extracted from `LevyStochCalc.Brownian.PolarisedQuadVar`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PolarisedQuadVar_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The polarised quadratic variation

For two integrands against the *same* Brownian motion, the product of the increments of their
Itô integrals, compensated by the window integral of the product of the integrands, is
conditionally centred at the left endpoint. The identity `2xy = (x+y)² − x² − y²` reduces this
to the compensated square increments of `H₁ + H₂`, of `H₁` and of `H₂`, using additivity of the
Itô integral in the integrand.

## Main statements

* `LevyStochCalc.Brownian.Ito.polarQuadVarIncrement` — the compensated product of increments.
* `LevyStochCalc.Brownian.Ito.smul_two_polarQuadVarIncrement_ae` — the polarisation identity.
* `LevyStochCalc.Brownian.Ito.condExp_polarQuadVarIncrement` — it is conditionally centred at
  the left endpoint.
* `LevyStochCalc.Brownian.Ito.integral_sq_polarQuadVarIncrement_le` — its second moment.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Polarised

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H₁ H₂ : Ω → ℝ → ℝ)
  (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
  (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
  (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
  (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
  (hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
  (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

section Bounds

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH₁ : ∀ ω s, |H₁ ω s| ≤ C) (hCH₂ : ∀ ω s, |H₂ ω s| ≤ C)

include hℱ hma hpa hqa hC0 hCH₁ hCH₂ in

theorem _root_.LevyStochCalc.Brownian.Ito.integral_sq_polarQuadVarIncrement_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Integrable (fun ω =>
        (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2) P
      ∧ ∫ ω, (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2 ∂P
        ≤ 3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4) * (b - a) ^ 2 := by sorry
