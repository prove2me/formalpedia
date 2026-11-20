-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_cross_sq_integrable
-- name    : LevyStochCalc.Brownian.Ito.cross_sq_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:10:31.544752+00:00
-- url     : https://prove2.me/theorems/837fedca-0770-4049-bc63-664548c13b25
-- title:
--   cross sq integrable
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.cross_sq_integrable` is extracted from `LevyStochCalc.Brownian.ItoSimpleMoments`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Filtered_F001
import Definitions.Def_LevyStochCalc_Brownian_Filtered_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments of the terms of the elementary Brownian integral

For an adapted simple predictable integrand the diagonal term satisfies
`E[(ξ_i · ΔW_i) ^ 2] = (t_{i+1} - t_i) · E[ξ_i ^ 2]`, where
`ΔW_i = W_{t_{i+1}} - W_{t_i}`, since `ΔW_i` is independent of `ℱ_{t_i}` and centred Gaussian
with variance `t_{i+1} - t_i`, while for `i < j` the off-diagonal term vanishes,
`E[(ξ_i · ΔW_i) · (ξ_j · ΔW_j)] = 0`. Both rest on the integrability of the squared increments
and of the cross products.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.cross_sq_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (i j : Fin H.N) :
    MeasureTheory.Integrable
      (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                          - W.W (H.partition i.castSucc) ω)) *
                (H.ξ j ω * (W.W (H.partition j.succ) ω
                          - W.W (H.partition j.castSucc) ω))) P := by sorry
