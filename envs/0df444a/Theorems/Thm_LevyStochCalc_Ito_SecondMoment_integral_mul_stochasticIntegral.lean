-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_SecondMoment_integral_mul_stochasticIntegral
-- name    : LevyStochCalc.Ito.SecondMoment.integral_mul_stochasticIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:32:33.513569+00:00
-- url     : https://prove2.me/theorems/30ed6741-4542-4f9a-8b1b-cc2e8e027f0f
-- title:
--   integral mul stochasticIntegral
-- statement:
--   The source theorem `LevyStochCalc.Ito.SecondMoment.integral_mul_stochasticIntegral` is extracted from `LevyStochCalc.Ito.SecondMomentQuadratic`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic second moment of an Itô–Lévy process

For an Itô–Lévy process `X_t = X₀ + ∫_0^t b ds + ∑_j ∫_0^t σ_j dW^j + ∫_0^t ∫_E γ dÑ` over a Lévy
driver, with a square-integrable initial value measurable at time zero and a square-integrable
progressive drift, the second moment at a time `T > 0` is

`𝔼[X_T²] = 𝔼[X₀²] + 2 ∫_0^T 𝔼[X_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j² ds + 𝔼 ∫_0^T ∫_E γ² dν ds`,

the expectation form of the quadratic Itô formula, under the `L²` hypotheses alone: no fourth
moment and no pathwise formula is used. Summing over the coordinates gives the vector form, and
the cross witness carried by the driver gives the form over its augmented joint natural
filtration. The polarised isometry for the compensated integral, the expected product of two
compensated integrals at a time being the expected time integral of the product of their
integrands against the Lévy measure, is proved here alongside.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section PolarisedMarked

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

theorem _root_.LevyStochCalc.Ito.SecondMoment.integral_mul_stochasticIntegral (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    {φ ψ : Ω → ℝ → E → ℝ}
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hψm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hψp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hψq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ∫ e, φ ω s e * ψ ω s e ∂ν ∂volume ∂P := by sorry
