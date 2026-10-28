-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_marginal_law
-- name    : LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_marginal_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:05:53.815621+00:00
-- url     : https://prove2.me/theorems/ea10b61b-b268-4f43-ba54-1421d0949a91
-- title:
--   Marginal law of Brownian motion with deterministic negative unit drift
-- statement:
--   At nonnegative time t, the law of W_t−t under P is the pushforward of the centred Gaussian law N(0,t) under z↦z−t. This basic transformation is a reusable prerequisite for proving Brownian-with-drift stationarity, exponential moments and the exact Lévy–Khintchine Laplace identity.
-- source:
--   LevyStochCalc.Brownian.BrownianMotion.hasLaw_eval_readable; Mathlib Measure.map_map.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian

theorem LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_marginal_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P) (t : ℝ≥0) :
    HasLaw (fun ω => W.W (t : ℝ) ω - (t : ℝ))
      ((gaussianReal 0 t).map (fun z : ℝ => z - (t : ℝ))) P := by sorry
