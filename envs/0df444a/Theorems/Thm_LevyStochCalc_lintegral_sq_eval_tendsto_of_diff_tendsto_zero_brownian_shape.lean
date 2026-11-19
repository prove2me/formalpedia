-- Prove2me | Theorems.Thm_LevyStochCalc_lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian_shape
-- name    : LevyStochCalc.lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian_shape
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T23:47:42.727391+00:00
-- url     : https://prove2.me/theorems/c7eb71f9-beae-48c4-90ec-3951038c5519
-- title:
--   lintegral sq eval tendsto of diff tendsto zero brownian shape
-- statement:
--   The source theorem `LevyStochCalc.lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian_shape` is extracted from `LevyStochCalc.Basic`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# LevyStochCalc.Basic

Common imports plus small L² helper lemmas shared across the library:
`eLpNorm` reverse-triangle / difference bounds and L²-continuity (Bochner-L²
limit) lemmas in the plain, Brownian, and compensated-Poisson integrand shapes.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc

theorem _root_.LevyStochCalc.lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian_shape
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {T : ℝ}
    (H : α → ℝ → ℝ) (h_H_meas : Measurable (Function.uncurry H))
    (ev : ℕ → ℝ → α → ℝ)
    (h_ev_meas : ∀ n, Measurable (fun (p : α × ℝ) => ev n p.2 p.1))
    (h_L2_diff : Filter.Tendsto
      (fun n => ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T,
        (‖H x y - ev n y x‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T,
        (‖ev n y x‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      Filter.atTop
      (nhds (∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T,
        (‖H x y‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)) := by sorry
