-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49PositiveInitialBlockV1
-- name    : Kyprianou.Ch04.exercise49PositiveInitialBlockV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:48:33.446262+00:00
-- url     : https://prove2.me/theorems/0ddd8e59-3cb5-48c6-a88e-bc152c45b7a9
-- title:
--   Positive small-time drift gives a nonnegative initial block with positive terminal gain and positive probability
-- statement:
--   Positive small-time drift gives a nonnegative initial block with positive terminal gain and positive probability
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49PositiveInitialBlockV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (d : ℝ) (hd : 0 < d)
    (hSlope : ∀ᵐ ω ∂P, Tendsto (fun t : NNReal => X t ω / (t : ℝ))
      (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds d)) :
    ∃ s : NNReal, 0 < s ∧ ∃ a : ℝ, 0 < a ∧
      0 < P {ω | (∀ t : NNReal, t ≤ s → 0 ≤ X t ω) ∧ a ≤ X s ω} := by
  sorry
