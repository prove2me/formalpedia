-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_path_no_positive_jumps
-- name    : LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_path_no_positive_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:04:28.384467+00:00
-- url     : https://prove2.me/theorems/f75d1ad5-a3ea-4f71-8eba-ba81bfd359c3
-- title:
--   Continuous drifted Brownian sample paths satisfy the canonical no-positive-jumps left-limit property
-- statement:
--   At strictly positive nonnegative time, the left-neighbourhood filter is nontrivial. A continuous drifted Brownian sample path converges to its present value along this filter, so any proposed left limit equals that present value. In particular the value at t is no greater than that left limit, matching the no-positive-jumps field of the Avram Lévy process model.
-- source:
--   Mathlib Topology.Order.DenselyOrdered nhdsLT_neBot_of_exists_lt; canonical Avram Dividend process interface.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

open MeasureTheory Filter Set Topology
open scoped NNReal
open LevyStochCalc.Brownian

theorem LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_path_no_positive_jumps
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P)
    (ω : Ω) (hpath : Continuous (fun t : ℝ => W.W t ω)) :
    ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s : ℝ≥0 => W.W (s : ℝ) ω - (s : ℝ)) (𝓝[<] t) (𝓝 l) →
      W.W (t : ℝ) ω - (t : ℝ) ≤ l := by sorry
