-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_MarkStep_integral_weight_incr_sq
-- name    : LevyStochCalc.Poisson.Compensated.MarkStep.integral_weight_incr_sq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T12:37:50.971556+00:00
-- url     : https://prove2.me/theorems/4fd28e2e-2b2f-43b6-8995-317b917b992f
-- title:
--   integral weight incr sq
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.integral_weight_incr_sq` is extracted from `LevyStochCalc.Poisson.MarkStepIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F000
import Definitions.Def_LevyStochCalc_Poisson_MarkStepWeight_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic mark-step integrands and their weighted increments

On the dyadic grids `TimeGrid.dyadic T hT n` of `[0, T]`, a mark-step integrand of level
`n` is re-expressed on any finer level `m ≥ n` (`MarkStep.dyadicRefine`), each fine piece
inheriting the coefficients of the coarse piece containing it, and is restricted to a
horizon `T'` with `T = T' * 2 ^ d` (`MarkStep.dyadicRestrict`); both leave the compensated
integral and the integrand unchanged. The increment of a mark-step integrand over `(s, t]`,
weighted by a bounded measurable `w`, is itself a mark-step integrand on the increment grid
`TimeGrid.incr` (`MarkStep.incr`), which gives the `L²` isometry for such increments.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Dyadic

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]

variable {T : ℝ} {hT : 0 < T} {n m : ℕ}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n))
  (hnm : n ≤ m)

end Dyadic

section Increment

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w) {s t : ℝ} (hs : 0 < s) (hst : s < t)

include hw hwm hs hst in
include hℱ in

theorem _root_.LevyStochCalc.Poisson.Compensated.MarkStep.integral_weight_incr_sq (hG : G.Adapted ℱ)
    (hwa : @StronglyMeasurable Ω ℝ _ (ℱ s) w) :
    ∫ ω, (w ω * (G.integral N t ω - G.integral N s ω)) ^ 2 ∂P
      = ∫ ω, (w ω) ^ 2 * (∫ e, ∫ σ in Set.Ioc s t, (G.eval σ e ω) ^ 2 ∂volume ∂ν) ∂P := by sorry
