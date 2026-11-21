-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_MarkStep_eval_dyadicRestrict
-- name    : LevyStochCalc.Poisson.Compensated.MarkStep.eval_dyadicRestrict
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T12:31:46.23321+00:00
-- url     : https://prove2.me/theorems/6b72e6be-9eee-4d53-89c7-f94703b67298
-- title:
--   eval dyadicRestrict
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.eval_dyadicRestrict` is extracted from `LevyStochCalc.Poisson.MarkStepIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F001

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

theorem _root_.LevyStochCalc.Poisson.Compensated.MarkStep.eval_dyadicRestrict {ℓ d : ℕ} (G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)) {T' : ℝ}
    (hT' : 0 < T') (hd : d ≤ ℓ) (h : T = T' * 2 ^ d) {s : ℝ} (hs : s ≤ T') (e : E) (ω : Ω) :
    (G.dyadicRestrict hT' hd h).eval s e ω = G.eval s e ω := by sorry
