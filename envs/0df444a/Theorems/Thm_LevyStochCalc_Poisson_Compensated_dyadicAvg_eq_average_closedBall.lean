-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_dyadicAvg_eq_average_closedBall
-- name    : LevyStochCalc.Poisson.Compensated.dyadicAvg_eq_average_closedBall
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T19:10:27.500214+00:00
-- url     : https://prove2.me/theorems/088fc854-7417-43fd-b805-42a8c1457e51
-- title:
--   dyadicAvg eq average closedBall
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.dyadicAvg_eq_average_closedBall` is extracted from `LevyStochCalc.Poisson.CompensatedDensityDyadic`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic time-discretisation of a mark-dependent integrand

The dyadic partition `tᵢ = i·T/2ⁿ` of `[0,T]`, the interval time-averages of a bounded
integrand `φ : Ω → ℝ → E → ℝ` with the mark carried as a parameter, and the piecewise-constant
evaluation `dyadicEval` built from them. For a bounded jointly measurable `φ`, the Lebesgue
density theorem gives almost-everywhere convergence of `dyadicEval` to `φ` in the time variable,
and dominated convergence upgrades it to convergence in `L²(P ⊗ ds ⊗ ν)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Dyadic time-discretisation (mark carried as a parameter)

The time direction is discretised by dyadic averaging, mirroring `Brownian/ItoDensity`,
but the integrand carries the mark `e`: the coefficient on the `k`-th dyadic interval is
the *previous*-interval time-average `(2ⁿ/T)∫_{tₖ₋₁}^{tₖ} φ(ω,u,e) du` (shifted left, so
it is `ℱ_{tₖ}`-measurable — adapted), evaluated as a function of `(ω, e)`. -/

omit [MeasurableSpace Ω] [MeasurableSpace E] in

theorem _root_.LevyStochCalc.Poisson.Compensated.dyadicAvg_eq_average_closedBall
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) (e : E) :
    dyadicAvg T φ n i ω e =
      ⨍ y in Metric.closedBall
        ((dyadicPartition T n i.castSucc + dyadicPartition T n i.succ) / 2)
        ((dyadicPartition T n i.succ - dyadicPartition T n i.castSucc) / 2),
        φ ω y e ∂volume := by sorry
