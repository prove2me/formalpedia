-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian
-- name    : LevyStochCalc.Brownian.Ito.lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T15:45:55.523949+00:00
-- url     : https://prove2.me/theorems/7c37dab7-03e9-446a-8cca-d7668078b9db
-- title:
--   lintegral sq eval tendsto of diff tendsto zero brownian
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian` is extracted from `LevyStochCalc.Brownian.ItoDensityUnbounded`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityUnbounded_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Density of the simple predictable processes in `L²`

Removal of the boundedness restriction by truncation: the `eLpNorm`/`lintegral`
dictionary on the product measure, and the density results `simplePredictable_dense_L2`
and `adaptedSimple_dense_L2_brownian` for an arbitrary square-integrable integrand.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian
    {μ : Measure Ω} [SFinite μ]
    {T : ℝ}
    (H : Ω → ℝ → ℝ) (h_H_meas : Measurable (Function.uncurry H))
    (ev : ℕ → ℝ → Ω → ℝ)
    (h_ev_meas : ∀ n, Measurable (fun (p : Ω × ℝ) => ev n p.2 p.1))
    (h_L2_diff : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)) := by sorry
