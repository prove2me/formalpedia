-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_restart_clock_ge
-- name    : Kyprianou.Ch08.StageB.p2m810_restart_clock_ge
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:47:44.888937+00:00
-- url     : https://prove2.me/theorems/92d44e08-2bcc-4a99-8e57-2e6dd374f748
-- title:
--   p2m810_restart_clock_ge
-- statement:
--   A component of the pathwise restart-clock identity: ((l-t : ℝ≥0) : WithTop ℝ≥0) ≤ lastNegativeVisit (fun s (_ : Unit) => y + X (t+s) ω) ()
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_restart_clock_ge :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (y : ℝ) (t l : ℝ≥0),
      tauMinus (shifted X y) 0 ω = (t : WithTop ℝ≥0) →
      lastExitShifted X y ω = (l : WithTop ℝ≥0) →
      ((l-t : ℝ≥0) : WithTop ℝ≥0) ≤ lastNegativeVisit (fun s (_ : Unit) => y + X (t+s) ω) () := by
  sorry
