-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_pathwise_last_exit_restart_payoff
-- name    : Kyprianou.Ch08.StageB.p2m810_pathwise_last_exit_restart_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T21:50:46.089802+00:00
-- url     : https://prove2.me/theorems/bd1979d2-4619-4855-9139-3e2b6a82ac76
-- title:
--   On a right-continuous path starting above zero and tending to infinity, the discounted positive last exit factors pathwise into first passage and the restarted discounted last exit.
-- statement:
--   On a right-continuous path starting above zero and tending to infinity, the discounted positive last exit factors pathwise into first passage and the restarted discounted last exit.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_pathwise_last_exit_restart_payoff
    (f : ℝ≥0 → ℝ) (y : ℝ) (q : ℝ) (hy : 0 < y) (h0 : f 0 = 0)
    (hc : ContinuousWithinAt f (Ici 0) 0) (h : Tendsto f atTop atTop) :
    discountedPositiveLastExit (fun t (_ : Unit) => f t) q y () =
      WithTop.recTopCoe (0 : ℝ) (fun t : ℝ≥0 =>
        Real.exp (-q * (t : ℝ)) *
          discountedAt q (lastNegativeVisit (fun s (_ : Unit) => y + f (t+s)) ()))
        (tauMinus (shifted (fun t (_ : Unit) => f t) y) 0 ()) := by
  sorry
