-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_simplePredictable_dense_L2
-- name    : LevyStochCalc.Brownian.Ito.simplePredictable_dense_L2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T15:45:59.831609+00:00
-- url     : https://prove2.me/theorems/0aec0bb8-c1df-453d-b15f-68f0939c1b91
-- title:
--   simplePredictable dense L2
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.simplePredictable_dense_L2` is extracted from `LevyStochCalc.Brownian.ItoDensityUnbounded`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F003

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

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

set_option maxHeartbeats 1600000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.LevyStochCalc.Brownian.Ito.simplePredictable_dense_L2
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) := by sorry
