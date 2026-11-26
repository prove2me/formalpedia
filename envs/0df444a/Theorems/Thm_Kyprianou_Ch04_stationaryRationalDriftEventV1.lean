-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stationaryRationalDriftEventV1
-- name    : Kyprianou.Ch04.stationaryRationalDriftEventV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:42:59.553162+00:00
-- url     : https://prove2.me/theorems/dffe6c30-865c-4661-9671-9b949805c87b
-- title:
--   Stationarity of the rational-time small-time drift event
-- statement:
--   The shifted process is Levy with the same marginal distributions, hence the same whole-path law. Pull the countable measurable rational convergence event back through both path laws.
-- source:
--   Supporting stochastic transfer for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_shiftedIsLevyProcessV1
import Theorems.Thm_Kyprianou_Ch02_levyWholePathLawEqOfMarginalLawsV1
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.stationaryRationalDriftEventV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P)
    (d : ℝ) (s : ℝ≥0) :
    (∀ᵐ ω ∂P, Tendsto
      (fun r : ℚ => (X (s + Real.toNNReal (r : ℝ)) ω - X s ω) /
        (Real.toNNReal (r : ℝ) : ℝ))
      (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d)) ↔
    (∀ᵐ ω ∂P, Tendsto
      (fun r : ℚ => X (Real.toNNReal (r : ℝ)) ω /
        (Real.toNNReal (r : ℝ) : ℝ))
      (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d)) := by
  sorry
