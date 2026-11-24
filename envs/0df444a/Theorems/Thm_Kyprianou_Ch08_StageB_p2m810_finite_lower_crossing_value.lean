-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_finite_lower_crossing_value
-- name    : Kyprianou.Ch08.StageB.p2m810_finite_lower_crossing_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:33:11.64834+00:00
-- url     : https://prove2.me/theorems/02171d08-a77c-4976-a66b-10633a1a7452
-- title:
--   Finite lower crossing attains at most the crossing level
-- statement:
--   Right continuity at a finite strict downcrossing infimum gives a value no greater than the threshold.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_finite_lower_crossing_value :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
      (l : ℝ) (u : ℝ≥0),
      ContinuousWithinAt (fun t => X t ω) (Ici u) u →
      tauMinus X l ω = (u : WithTop ℝ≥0) → X u ω ≤ l := by
  sorry
