-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_predictableDyadicSimple_brownian_eval_jointly_measurable
-- name    : LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_eval_jointly_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T15:43:26.218351+00:00
-- url     : https://prove2.me/theorems/385c7a93-ff2f-420b-86c4-e0d8e23f42fb
-- title:
--   predictableDyadicSimple brownian eval jointly measurable
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_eval_jointly_measurable` is extracted from `LevyStochCalc.Brownian.ItoDensityPredictableL2`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F001

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

theorem _root_.LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_eval_jointly_measurable
    {T : ℝ} (hT : 0 < T) (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    Measurable (fun (p : Ω × ℝ) =>
      (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by sorry
