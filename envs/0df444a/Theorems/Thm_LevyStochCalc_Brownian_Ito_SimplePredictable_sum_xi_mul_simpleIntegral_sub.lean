-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_sum_xi_mul_simpleIntegral_sub
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.sum_xi_mul_simpleIntegral_sub
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T17:42:23.097541+00:00
-- url     : https://prove2.me/theorems/8b934032-3250-44c0-87e1-00061e8458ea
-- title:
--   sum xi mul simpleIntegral sub
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.sum_xi_mul_simpleIntegral_sub` is extracted from `LevyStochCalc.Brownian.ItoAlgebraProduct`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Products of simple integrands and elementary integrals against a process

Two simple integrands with a common final partition point multiply to a simple integrand carried
on their common refinement, whose evaluation is the pointwise product of the evaluations and
whose adaptedness is inherited; summing the increments of the elementary integral of one against
the coefficients of the other is the elementary integral of that product, and the difference
between an elementary integral and an `L²` Itô integral obeys the Itô isometry.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.SimplePredictable.sum_xi_mul_simpleIntegral_sub
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (G K : SimplePredictable Ω T)
    (h_eq : G.partition (Fin.last G.N) = K.partition (Fin.last K.N))
    (t : ℝ) (ω : Ω) :
    (∑ i : Fin G.N, G.ξ i ω *
        (simpleIntegral W K (min (G.partition i.succ) t) ω
          - simpleIntegral W K (min (G.partition i.castSucc) t) ω))
      = simpleIntegral W (G.mul_on_common K h_eq) t ω := by sorry
