-- Prove2me | Theorems.Thm_Kyprianou_Ch04_pathRunningInfimumLimit
-- name    : Kyprianou.Ch04.pathRunningInfimumLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:15:28.547274+00:00
-- url     : https://prove2.me/theorems/4c2cb855-d80f-450c-a8c8-b2cd568e8e57
-- title:
--   Running infimum tends to all-time infimum on bounded paths
-- statement:
--   The finite-horizon infima decrease and are bounded below by the global infimum. Each path value occurs in its own horizon, identifying the infimum of the horizon infima.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
open Set Filter
open scoped NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.pathRunningInfimumLimit (x : NNReal → ℝ) (hbd : BddBelow (range x)) :
    Tendsto (fun t : NNReal => sInf (x '' Iic t)) atTop (nhds (sInf (range x))) := by
  sorry
