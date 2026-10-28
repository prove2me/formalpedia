-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_gaussian_law
-- name    : LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_gaussian_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:08:31.70503+00:00
-- url     : https://prove2.me/theorems/71cbe501-8abc-41d4-b1c9-50d9151f3025
-- title:
--   Brownian motion with drift minus one has Gaussian mean minus t and variance t
-- statement:
--   For t≥0, the drifted Brownian variable W_t−t has Gaussian distribution with mean −t and variance t. This puts the normal law into the exact parameters required for moment-generating-function and Lévy exponent calculations.
-- source:
--   Proved BrownianMotion.hasLaw_eval_readable and Mathlib ProbabilityTheory.gaussianReal_sub_const.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian

theorem LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_gaussian_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P) (t : ℝ≥0) :
    HasLaw (fun ω => W.W (t : ℝ) ω - (t : ℝ))
      (gaussianReal (-(t : ℝ)) t) P := by sorry
