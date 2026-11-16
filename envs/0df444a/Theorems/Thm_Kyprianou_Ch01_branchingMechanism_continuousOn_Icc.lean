-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingMechanism_continuousOn_Icc
-- name    : Kyprianou.Ch01.branchingMechanism_continuousOn_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T18:07:31.337566+00:00
-- url     : https://prove2.me/theorems/b8aea076-24e5-4c77-b431-a058ae3d3704
-- title:
--   Local continuity of branching mechanism via uniformly dominated PMF series
-- statement:
--   The infinite offspring PMF series defining the branching mechanism is uniformly dominated on each nonnegative compact interval [a,b] by a common summable weight; continuity of summands and uniform convergence establish local continuity.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11(iii), branching mechanism convergence and continuity

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingMechanism_continuousOn_Icc
    (rate : ℝ) (offspring : PMF ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ContinuousOn (branchingMechanism rate offspring) (Icc a b) := by sorry
