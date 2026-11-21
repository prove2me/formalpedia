-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_stochasticIntegral_add
-- name    : LevyStochCalc.Poisson.Compensated.stochasticIntegral_add
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:14:27.980171+00:00
-- url     : https://prove2.me/theorems/1ebfacdb-4df3-4842-b8fd-77053611d5d3
-- title:
--   stochasticIntegral add
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.stochasticIntegral_add` is extracted from `LevyStochCalc.Poisson.CompensatedLinear`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the compensated Poisson integral

The compensated integral is built as an `L²` limit of elementary integrals, which is not itself a
linear construction, so linearity comes from the isometries instead: they fix every squared
`L²`-distance among the integrals of two integrands and of their sum, and the parallelogram law
for the marked energies then forces the sum relation. The same three-distance argument gives the
scalar rule.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Parallelogram

variable {φ₁ φ₂ : Ω → ℝ → E → ℝ}

end Parallelogram

section Linearity

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)

include hℱ in

theorem _root_.LevyStochCalc.Poisson.Compensated.stochasticIntegral_add {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hp₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (hp₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (hq₁ : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ₁ < ⊤)
    (hq₂ : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ₂ < ⊤)
    (hma : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 + φ₂ p.1 p.2.1 p.2.2)
    (hpa : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => φ₁ ω s e + φ₂ ω s e)
    (hqa : ∀ T : ℝ, 0 < T → markedEnergy P ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e) < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegral N ℱ hℱ (fun ω s e => φ₁ ω s e + φ₂ ω s e) hma hpa hqa T
      =ᵐ[P] fun ω => stochasticIntegral N ℱ hℱ φ₁ hm₁ hp₁ hq₁ T ω
        + stochasticIntegral N ℱ hℱ φ₂ hm₂ hp₂ hq₂ T ω := by sorry
