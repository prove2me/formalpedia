-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_eval_sq
-- name    : LevyStochCalc.Brownian.Ito.lintegral_eval_sq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T20:44:55.890125+00:00
-- url     : https://prove2.me/theorems/ed3a2d4f-51f5-4977-ab8d-28610e73c9ab
-- title:
--   lintegral eval sq
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.lintegral_eval_sq` is extracted from `LevyStochCalc.Brownian.ItoSimpleIntegrand`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple predictable integrands and the elementary Brownian integral

The class `SimplePredictable` of integrands `∑_i ξ_i · 1_{(t_i, t_{i+1}]}` with bounded
measurable coefficients, their pointwise evaluation `SimplePredictable.eval`, the elementary
integral `simpleIntegral` against a scalar Brownian motion `W`, and the energy
`∫⁻ ‖H.eval s ω‖₊ ^ 2` of the integrand, which the disjointness of the partition intervals
`(t_i, t_{i+1}]` turns into the sum `∑_i (t_{i+1} - t_i) · ∫⁻ ‖ξ_i‖₊ ^ 2 ∂P`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.lintegral_eval_sq {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∑ i : Fin H.N,
        ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
        (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 := by sorry
