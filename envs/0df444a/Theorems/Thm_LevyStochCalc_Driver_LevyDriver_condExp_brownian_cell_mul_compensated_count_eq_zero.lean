-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_condExp_brownian_cell_mul_compensated_count_eq_zero
-- name    : LevyStochCalc.Driver.LevyDriver.condExp_brownian_cell_mul_compensated_count_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:56:00.716905+00:00
-- url     : https://prove2.me/theorems/e66b12b8-571b-4842-b2f8-33a24ca089d8
-- title:
--   condExp brownian cell mul compensated count eq zero
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.condExp_brownian_cell_mul_compensated_count_eq_zero` is extracted from `LevyStochCalc.Driver.CellConditionalIsometryPoisson`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellConditionalIsometry_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Conditional cell isometries against the compensated Poisson random measure

Over a cell `(a, b]` with `0 ≤ a < b` and a mark set `A` of finite intensity, the increment of a
compensated integral across `(a, b]` pairs with the compensated count `Ñ((a, b] × A)` to the
integral of the integrand over the cell and over `A`, and the pairing survives conditioning at
the left endpoint. The compensated count is the compensated integral of the indicator integrand
of the rectangle `(a, b] × A`, restricting the integrand to the cell turns the increment into the
integral at the horizon `b`, a bounded weight measurable at `a` passes inside, and the horizon
isometry then evaluates the pairing.

## Main statements

* `stochasticIntegral_cellMarkIndicator_ae_eq` — the compensated count of `(a, b] × A` is the
  compensated integral of the indicator integrand of that rectangle.
* `condExp_compensated_cell_mul_compensated_count` — the conditional Itô–Lévy isometry over a
  cell, against the compensated count of `(a, b] × A`.
* `condExp_brownian_cell_mul_compensated_count_eq_zero` — a Brownian cell increment is
  conditionally orthogonal to the compensated count of `(a, b] × A`.

## References

* Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open LevyStochCalc.Brownian.Ito (indIoc)

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section CompensatedCell

variable {φ : Ω → ℝ → E → ℝ} {A : Set E}

theorem _root_.LevyStochCalc.Driver.LevyDriver.condExp_brownian_cell_mul_compensated_count_eq_zero (𝒲 : CrossWitness D ℱ) {i : Fin d}
    (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
    (hℱN : Poisson.IsPoissonFiltration D.N ℱ)
    {H : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[fun ω =>
        (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * D.N.compensated (Set.Ioc a b ×ˢ A) ω | ℱ a] =ᵐ[P] 0 := by sorry
