-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_compensatedIntegral_congr_ae
-- name    : LevyStochCalc.Ito.Picard.compensatedIntegral_congr_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:14:32.834177+00:00
-- url     : https://prove2.me/theorems/84d211ba-5d46-481d-af73-9eafa8ae7d08
-- title:
--   compensatedIntegral congr ae
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.compensatedIntegral_congr_ae` is extracted from `LevyStochCalc.Ito.PicardLocality`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardSupL2_F000

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

theorem _root_.LevyStochCalc.Ito.Picard.compensatedIntegral_congr_ae {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ₁ φ₂ : Ω → ℝ → E → ℝ)
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hp₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (hs₁ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hp₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (hs₂ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), φ₁ ω s = φ₂ ω s) :
    ∀ᵐ ω ∂P,
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
        = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω := by sorry
