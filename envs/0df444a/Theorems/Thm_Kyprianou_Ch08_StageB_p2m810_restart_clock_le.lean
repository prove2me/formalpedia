-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_restart_clock_le
-- name    : Kyprianou.Ch08.StageB.p2m810_restart_clock_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:47:43.28435+00:00
-- url     : https://prove2.me/theorems/115949da-0b89-4748-a4fa-edfce727882b
-- title:
--   p2m810_restart_clock_le
-- statement:
--   A component of the pathwise restart-clock identity: lastNegativeVisit (fun s (_ : Unit) => y + X (t+s) ω) () ≤ ((l-t : ℝ≥0) : WithTop ℝ≥0)
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_restart_clock_le :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (y : ℝ) (t l : ℝ≥0),
      tauMinus (shifted X y) 0 ω = (t : WithTop ℝ≥0) →
      lastExitShifted X y ω = (l : WithTop ℝ≥0) →
      lastNegativeVisit (fun s (_ : Unit) => y + X (t+s) ω) () ≤ ((l-t : ℝ≥0) : WithTop ℝ≥0) := by
  sorry
