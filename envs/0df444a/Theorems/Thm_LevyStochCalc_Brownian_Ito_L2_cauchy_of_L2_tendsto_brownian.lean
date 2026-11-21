-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_L2_cauchy_of_L2_tendsto_brownian
-- name    : LevyStochCalc.Brownian.Ito.L2_cauchy_of_L2_tendsto_brownian
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T12:22:55.662151+00:00
-- url     : https://prove2.me/theorems/59002088-c55b-402e-bec2-7b8f122f8c8e
-- title:
--   L2 cauchy of L2 tendsto brownian
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.L2_cauchy_of_L2_tendsto_brownian` is extracted from `LevyStochCalc.Brownian.ItoDensityPredictableL2`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F002

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

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

set_option maxHeartbeats 1600000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.LevyStochCalc.Brownian.Ito.L2_cauchy_of_L2_tendsto_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ}
    (Hn : ℕ → SimplePredictable Ω T)
    (H : Ω → ℝ → ℝ)
    (h_meas_eval : ∀ n, Measurable (fun (p : Ω × ℝ) => (Hn n).eval p.2 p.1))
    (h_meas_H : Measurable (Function.uncurry H))
    (h_tendsto : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(Hn n).eval s ω - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε := by sorry
