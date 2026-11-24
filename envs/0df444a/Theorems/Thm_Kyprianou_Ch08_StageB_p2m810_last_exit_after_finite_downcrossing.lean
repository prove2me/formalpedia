-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_last_exit_after_finite_downcrossing
-- name    : Kyprianou.Ch08.StageB.p2m810_last_exit_after_finite_downcrossing
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:34:23.322801+00:00
-- url     : https://prove2.me/theorems/f4532585-dfd8-4a2e-ab0c-e69d5ebe62ac
-- title:
--   Finite last-exit time decomposes after the finite downcrossing
-- statement:
--   For a path with finite first negative passage and finite last negative visit, the latter minus the former is exactly the last strictly positive negative-visit time of the restarted path.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_last_exit_after_finite_downcrossing :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (y : ℝ) (t l : ℝ≥0),
      tauMinus (shifted X y) 0 ω = (t : WithTop ℝ≥0) →
      lastExitShifted X y ω = (l : WithTop ℝ≥0) →
      t ≤ l ∧
        lastNegativeVisit (fun s (_ : Unit) => y + X (t+s) ω) () =
          ((l-t : ℝ≥0) : WithTop ℝ≥0) := by
  sorry
