-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_stochasticIntegral_congr_ae
-- name    : LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:15:41.938186+00:00
-- url     : https://prove2.me/theorems/b81aec88-34cc-4314-933c-1cf4a5c69a5b
-- title:
--   stochasticIntegral congr ae
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_ae` is extracted from `LevyStochCalc.Poisson.CompensatedCongr`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral depends only on the class of its integrand

Two admissible marked integrands that agree almost everywhere for the product of the sample
measure, Lebesgue measure on the horizon and the mark measure have almost surely equal
compensated integrals: the energy of their difference vanishes, and the difference isometry
turns that into an almost sure identity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

theorem _root_.LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_ae (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (φ ψ : Ω → ℝ → E → ℝ)
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hψm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hψp : Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hφq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hψq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (h : (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
      =ᵐ[markedEnergyMeasure P ν T] fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2) :
    stochasticIntegral N ℱ hℱ φ hφm hφp hφq T
      =ᵐ[P] stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T := by sorry
