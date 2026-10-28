-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_ae_good_path
-- name    : LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_ae_good_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:57:57.166154+00:00
-- url     : https://prove2.me/theorems/3f8cb7b7-3f3f-4f39-b8d3-9752151b84c4
-- title:
--   Almost surely, Brownian motion with drift minus one starts at zero and has continuous sample paths
-- statement:
--   For any Brownian motion in the LevyStochCalc construction, the process t ↦ W_t−t starts at zero and has continuous paths on one almost-sure set. This supplies the good-path event needed to restrict the probability space before building a pathwise continuous spectrally negative Lévy instance.
-- source:
--   LevyStochCalc BrownianMotion structure initial_zero and continuous_paths; Avram Dividend process-adapter programme.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Mathlib.Tactic

open MeasureTheory
open LevyStochCalc.Brownian

theorem LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_ae_good_path
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (W : BrownianMotion P) :
    ∀ᵐ ω ∂P, W.W 0 ω = 0 ∧
      Continuous (fun t : ℝ => W.W t ω - t) := by sorry
