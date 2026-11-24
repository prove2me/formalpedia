-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_reset_squeeze
-- name    : Kyprianou.Ch08.StageB.p2m810_inf_reset_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:12:34.058924+00:00
-- url     : https://prove2.me/theorems/6641bc59-e009-4144-9828-11f70e99217d
-- title:
--   One-sided limit sandwich for reset approximations
-- statement:
--   The lower and upper reset bounds have the same limit; at x=a use the bound F≤1.
-- source:
--   Kyprianou (2006), Theorem 8.10.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- One-sided limit sandwich for reset approximations -/
theorem p2m810_inf_reset_squeeze :
    ∀ (R : ℝ → ℝ → ℝ) (F L x a : ℝ),
      0 < a → x ≤ a → F ≤ 1 → (x = a → L = 1) →
      (∀ ε : ℝ, 0 < ε → ε < a →
        R ε a ≤ F ∧ (x ≤ a-ε → F ≤ R ε (a-ε))) →
      Tendsto (fun ε => R ε a) (nhdsWithin 0 (Ioi 0)) (nhds L) →
      Tendsto (fun ε => R ε (a-ε)) (nhdsWithin 0 (Ioi 0)) (nhds L) →
      F = L := by
  sorry
end Kyprianou.Ch08.StageB
