-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_path_rightCont_leftLim
-- name    : LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_path_rightCont_leftLim
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:00:11.157379+00:00
-- url     : https://prove2.me/theorems/4e8a5396-a47b-4108-b6ab-4acd5af1f373
-- title:
--   Continuous drifted Brownian sample path has right continuity and left limits on nonnegative time
-- statement:
--   Given a continuous sample path of a Brownian motion, the drifted restriction to nonnegative times t ↦ W_t−t is continuous. It therefore satisfies the exact right-continuity and finite-left-limit interfaces demanded by the canonical spectrally negative Lévy process structure.
-- source:
--   LevyStochCalc BrownianMotion, canonical Avram Dividend SpectrallyNegativeLevy pathwise regularity interface.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Mathlib.Tactic

open MeasureTheory Filter Set Topology
open scoped NNReal
open LevyStochCalc.Brownian

theorem LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_path_rightCont_leftLim
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P)
    (ω : Ω) (hpath : Continuous (fun t : ℝ => W.W t ω)) :
    (∀ t : ℝ≥0, ContinuousWithinAt
      (fun s : ℝ≥0 => W.W (s : ℝ) ω - (s : ℝ)) (Ici t) t) ∧
    (∀ t : ℝ≥0, 0 < t → ∃ l : ℝ,
      Tendsto (fun s : ℝ≥0 => W.W (s : ℝ) ω - (s : ℝ)) (𝓝[<] t) (𝓝 l)) := by sorry
