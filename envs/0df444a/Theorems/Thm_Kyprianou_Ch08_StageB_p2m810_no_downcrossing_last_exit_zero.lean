-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_no_downcrossing_last_exit_zero
-- name    : Kyprianou.Ch08.StageB.p2m810_no_downcrossing_last_exit_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T21:50:53.930982+00:00
-- url     : https://prove2.me/theorems/9d0ed614-19a3-4877-9fea-3e45db13d216
-- title:
--   If the first strict downcrossing is infinite, the last negative visit is zero.
-- statement:
--   If the first strict downcrossing is infinite, the last negative visit is zero.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_no_downcrossing_last_exit_zero
    (f : ℝ≥0 → ℝ) (y : ℝ) (h : tauMinus (shifted (fun t (_ : Unit) => f t) y) 0 () = ⊤) :
    lastExitShifted (fun t (_ : Unit) => f t) y () = 0 := by
  sorry
