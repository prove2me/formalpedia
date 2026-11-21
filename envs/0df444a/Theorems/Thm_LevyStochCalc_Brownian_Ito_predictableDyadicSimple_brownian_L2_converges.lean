-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_predictableDyadicSimple_brownian_L2_converges
-- name    : LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_L2_converges
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T12:56:41.507863+00:00
-- url     : https://prove2.me/theorems/d1015f08-fa2c-4719-83ca-21eec473a53d
-- title:
--   predictableDyadicSimple brownian L2 converges
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_L2_converges` is extracted from `LevyStochCalc.Brownian.ItoDensityPredictableL2`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# `L²` convergence of the predictable dyadic approximations

For a bounded jointly measurable integrand the left-shifted dyadic simple processes
converge to it in `L²(Ω × [0,T])`, giving density of the simple predictable processes and
of the adapted simple processes in the bounded case, joint measurability of the evaluation
map and the `L²` Cauchy property of the approximating sequence.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_L2_converges
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s - (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by sorry
