-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stationaryRationalDriftAtOriginV1
-- name    : Kyprianou.Ch04.stationaryRationalDriftAtOriginV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:46:22.47741+00:00
-- url     : https://prove2.me/theorems/c80db936-aedd-4d8f-8ff9-34d94aa8700f
-- title:
--   Stationary rational slope limit at the origin by Fubini
-- statement:
--   Use a jointly measurable indistinguishable version for the rational increment slope event, apply Fubini on the positive unit interval, and transfer the full-measure event to the origin by stationary path law.
-- source:
--   Supporting stochastic transfer for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.stationaryRationalDriftAtOriginV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P) (d : ℝ)
    (hA : ∀ᵐ ω ∂P, ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      Tendsto (fun r : ℚ =>
        (X (Real.toNNReal s + Real.toNNReal (r : ℝ)) ω - X (Real.toNNReal s) ω) /
          (Real.toNNReal (r : ℝ) : ℝ))
        (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun r : ℚ => X (Real.toNNReal (r : ℝ)) ω / (Real.toNNReal (r : ℝ) : ℝ))
      (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d) := by
  sorry
