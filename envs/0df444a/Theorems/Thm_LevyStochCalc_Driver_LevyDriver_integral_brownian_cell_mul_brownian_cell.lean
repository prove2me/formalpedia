-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_integral_brownian_cell_mul_brownian_cell
-- name    : LevyStochCalc.Driver.LevyDriver.integral_brownian_cell_mul_brownian_cell
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:51:58.581458+00:00
-- url     : https://prove2.me/theorems/ad48f726-731d-49c4-b170-26468a6b4ce2
-- title:
--   integral brownian cell mul brownian cell
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.integral_brownian_cell_mul_brownian_cell` is extracted from `LevyStochCalc.Driver.CellConditionalIsometry`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellConditionalIsometry_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Conditional cell isometries for a Lévy driver

Over a cell `(a, b]` with `0 ≤ a < b` the increment of a Brownian Itô integral pairs with a
second such increment to the time integral of the product of the integrands over the cell, and
the pairing survives conditioning at the left endpoint: the conditional expectation at `ℱ a` of
the increment against the Brownian increment `W_b − W_a` is the conditional cell average of the
integrand. Restricting the integrand to the cell turns the increment into the integral at the
horizon `b`, a bounded weight measurable at `a` passes inside, and the horizon isometry then
evaluates the pairing.

## Main statements

* `integral_brownian_cell_mul_brownian_cell` — the polarised Itô isometry over a cell.
* `condExp_brownian_cell_mul_increment` — the conditional Itô isometry over a cell, against the
  Brownian increment.
* `condExp_brownian_cell_mul_brownian_increment_eq_zero` — the increment against one coordinate
  is conditionally orthogonal to the increment of another coordinate.

## References

* Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open LevyStochCalc.Brownian.Ito (indIoc)

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section BrownianCell

variable {H K : Ω → ℝ → ℝ}

theorem _root_.LevyStochCalc.Driver.LevyDriver.integral_brownian_cell_mul_brownian_cell
    (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {i : Fin d}
    (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K)
    (hKs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
        - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
      * (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) K hKm hKp hKs b ω
        - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) K hKm hKp hKs a ω) ∂P
      = ∫ ω, ∫ s in Set.Ioc a b, H ω s * K ω s ∂volume ∂P := by sorry
