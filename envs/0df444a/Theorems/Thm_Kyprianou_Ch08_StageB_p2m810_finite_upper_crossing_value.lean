-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_finite_upper_crossing_value
-- name    : Kyprianou.Ch08.StageB.p2m810_finite_upper_crossing_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:44:12.819222+00:00
-- url     : https://prove2.me/theorems/ee058481-576d-4d77-bf7b-eb0f6a2a5b01
-- title:
--   Finite upper crossing attains at least the crossing level
-- statement:
--   Right continuity at the finite infimum of the strict upcrossing set implies the path is at least the level there.
-- source:
--   Kyprianou (2006), Theorem 8.10(i); actual height law of Theorem 8.2.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Finite upper crossing attains at least the crossing level -/
theorem p2m810_finite_upper_crossing_value :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
      (l : ℝ) (u : ℝ≥0),
      ContinuousWithinAt (fun t => X t ω) (Ici u) u →
      tauPlus X l ω = (u : WithTop ℝ≥0) → l ≤ X u ω := by
  sorry
end Kyprianou.Ch08.StageB
