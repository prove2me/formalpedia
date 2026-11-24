-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_monotone_path_no_drawdown
-- name    : Kyprianou.Ch08.StageB.p2m810_monotone_path_no_drawdown
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:30:07.75883+00:00
-- url     : https://prove2.me/theorems/23ffc5ae-146d-4d0f-ad5d-a13522353dd2
-- title:
--   Monotone paths have no strict drawdown above initial level
-- statement:
--   A monotone path starting from zero has running maximum equal to its current value. Its drawdown from an initial maximum x is therefore at most x.
-- source:
--   Kyprianou (2006), Theorem 8.10(i), zero right slope.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Monotone paths have no strict drawdown above initial level -/
theorem p2m810_monotone_path_no_drawdown :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (x a : ℝ),
      X 0 ω = 0 → Monotone (fun t : ℝ≥0 => X t ω) →
      0 ≤ x → x ≤ a → reflectedSupExit X x a ω = ⊤ := by
  sorry
end Kyprianou.Ch08.StageB
