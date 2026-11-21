-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_stochasticIntegral_const_mul
-- name    : LevyStochCalc.Poisson.Compensated.stochasticIntegral_const_mul
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:16:06.23165+00:00
-- url     : https://prove2.me/theorems/90f50a15-9e9c-4110-9d5a-23c6574c1845
-- title:
--   stochasticIntegral const mul
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.stochasticIntegral_const_mul` is extracted from `LevyStochCalc.Poisson.CompensatedLinear`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F002

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

theorem _root_.LevyStochCalc.Poisson.Compensated.stochasticIntegral_const_mul {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤) (c : ℝ)
    (hmc : Measurable fun p : Ω × ℝ × E => c * φ p.1 p.2.1 p.2.2)
    (hpc : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => c * φ ω s e)
    (hqc : ∀ T : ℝ, 0 < T → markedEnergy P ν T (fun ω s e => c * φ ω s e) < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegral N ℱ hℱ (fun ω s e => c * φ ω s e) hmc hpc hqc T
      =ᵐ[P] fun ω => c * stochasticIntegral N ℱ hℱ φ hm hp hq T ω := by sorry
