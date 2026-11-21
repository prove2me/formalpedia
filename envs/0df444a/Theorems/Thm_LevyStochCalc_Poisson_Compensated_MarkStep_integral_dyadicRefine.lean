-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_MarkStep_integral_dyadicRefine
-- name    : LevyStochCalc.Poisson.Compensated.MarkStep.integral_dyadicRefine
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T12:30:00.970258+00:00
-- url     : https://prove2.me/theorems/e1a69cd4-9ae4-464f-91c2-698a67cbafef
-- title:
--   integral dyadicRefine
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.integral_dyadicRefine` is extracted from `LevyStochCalc.Poisson.MarkStepIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F000

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

include hℱ in

theorem _root_.LevyStochCalc.Poisson.Compensated.MarkStep.integral_dyadicRefine (hG : G.Adapted ℱ) (t : ℝ) :
    (fun ω => (G.dyadicRefine hnm).integral N t ω) =ᵐ[P] fun ω => G.integral N t ω := by sorry
