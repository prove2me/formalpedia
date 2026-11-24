-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_record_survival_path_lower_bound
-- name    : Kyprianou.Ch08.StageB.p2m810_record_survival_path_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:30:01.91275+00:00
-- url     : https://prove2.me/theorems/571b5489-94da-41e1-81df-47c3ba658b60
-- title:
--   Survival of every positive record forces a pathwise lower bound
-- statement:
--   If the path ever falls below -a, its drawdown exceeds a and its exit clock is no later than that time. The path is bounded above on that compact time interval. A record level above that bound cannot precede the exit.
-- source:
--   Kyprianou (2006), Theorem 8.10(i), zero right slope.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Survival of every positive record forces a pathwise lower bound -/
theorem p2m810_record_survival_path_lower_bound :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (a : ℝ),
      0 ≤ a → X 0 ω = 0 →
      (∀ T : ℝ≥0, BddAbove {z : ℝ | ∃ s : ℝ≥0, s ≤ T ∧ z = X s ω}) →
      (∀ n : ℕ, tauPlus X ((n : ℝ)+1) ω < reflectedSupExit X 0 a ω) →
      ∀ t : ℝ≥0, -a ≤ X t ω := by
  sorry
end Kyprianou.Ch08.StageB
