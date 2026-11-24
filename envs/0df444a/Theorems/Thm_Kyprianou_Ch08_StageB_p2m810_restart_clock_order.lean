-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_restart_clock_order
-- name    : Kyprianou.Ch08.StageB.p2m810_restart_clock_order
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:47:27.420458+00:00
-- url     : https://prove2.me/theorems/df707698-6aa0-445a-ae84-eebd2a8fbf60
-- title:
--   p2m810_restart_clock_order
-- statement:
--   A component of the pathwise restart-clock identity: t ≤ l
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_restart_clock_order :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (y : ℝ) (t l : ℝ≥0),
      tauMinus (shifted X y) 0 ω = (t : WithTop ℝ≥0) →
      lastExitShifted X y ω = (l : WithTop ℝ≥0) →
      t ≤ l := by
  sorry
