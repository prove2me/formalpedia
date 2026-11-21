-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_condExp_brownian_cell_mul_increment
-- name    : LevyStochCalc.Driver.LevyDriver.condExp_brownian_cell_mul_increment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:48:19.623774+00:00
-- url     : https://prove2.me/theorems/961979dc-d906-4eaf-b580-8a4e4b122f74
-- title:
--   condExp brownian cell mul increment
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.condExp_brownian_cell_mul_increment` is extracted from `LevyStochCalc.Driver.CellConditionalIsometry`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellOrthogonality_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F001

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

theorem _root_.LevyStochCalc.Driver.LevyDriver.condExp_brownian_cell_mul_increment
    (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {i : Fin d}
    (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[fun ω =>
        (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * ((D.W.W i).W b ω - (D.W.W i).W a ω) | ℱ a]
      =ᵐ[P] P[fun ω => ∫ s in Set.Ioc a b, H ω s ∂volume | ℱ a] := by sorry
