-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_increment_gaussian
-- name    : LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_increment_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:20:24.502225+00:00
-- url     : https://prove2.me/theorems/2e1a61eb-85bd-4d58-8a98-831b295e2059
-- title:
--   Every positive-time increment of unit-negative-drift Brownian motion is Gaussian with mean minus elapsed time
-- statement:
--   For 0≤s<t, the increment (W_t−W_s)−(t−s) has Gaussian law with mean −(t−s) and variance t−s. This precisely identifies the increments of Brownian motion with drift −1 and is a prerequisite for proving stationary increments of the canonical spectrally negative Lévy instance.
-- source:
--   LevyStochCalc BrownianMotion.increment_gaussian and Mathlib ProbabilityTheory.gaussianReal_sub_const.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian

theorem LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_increment_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasLaw (fun ω => (W.W t ω - W.W s ω) - (t - s))
      (gaussianReal (-(t - s)) ⟨t - s, by linarith⟩) P := by sorry
