-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_masterApprox_tendsto_L2
-- name    : LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:14:39.214179+00:00
-- url     : https://prove2.me/theorems/fd3db216-fbb7-4ad4-9623-d2a608f5e284
-- title:
--   masterApprox tendsto L2
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionMaster`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the master approximating sequence

The master sequence `masterApprox` of adapted simple predictable integrands on the
growing horizons `[0, n + 1]`, its Cauchy property in `L²(P)` uniformly on compact
time intervals, the limit `masterLp` and `stochasticIntegralBrownianLp` in
`Lp ℝ 2 P`, and the process `stochasticIntegralBrownian` together with its
adaptedness, vanishing on negative times and `ℱ`-martingale property.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2 {t : ℝ} (ht_nn : 0 ≤ t) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) 2 P)
      Filter.atTop (nhds 0) := by sorry
