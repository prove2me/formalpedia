-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_itoIntegral_congr_ae
-- name    : LevyStochCalc.Ito.Picard.itoIntegral_congr_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:17:03.08518+00:00
-- url     : https://prove2.me/theorems/46cba9a7-3ef3-43b2-a421-d93c5bbf61bf
-- title:
--   itoIntegral congr ae
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.itoIntegral_congr_ae` is extracted from `LevyStochCalc.Ito.PicardLocality`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardLocality_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Locality of the Picard step

The Picard step at time `t` reads its input only on `[0, t]`: the drift is a Bochner integral
over `Set.Icc 0 t`, and the two stochastic components are `L²` integrals whose difference
isometries turn an a.e. vanishing integrand into an a.e. vanishing integral. Consequently two
input paths agreeing `volume ⊗ P`-a.e. on `[0, t]` produce a.e. equal steps at `t`, which is
what identifies a window solution with the solution on any longer window.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Slice measurability of the two stochastic integrals -/

/-! ### An a.e. vanishing integrand has an a.e. vanishing energy -/

/-! ### Locality of the two stochastic integrals -/

theorem _root_.LevyStochCalc.Ito.Picard.itoIntegral_congr_ae
    (Wj : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration Wj ℱ)
    (H₁ H₂ : Ω → ℝ → ℝ)
    (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hs₁ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hs₂ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), H₁ ω s = H₂ ω s) :
    ∀ᵐ ω ∂P, LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
      = LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω := by sorry
