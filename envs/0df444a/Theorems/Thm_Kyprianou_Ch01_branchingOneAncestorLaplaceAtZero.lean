-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorLaplaceAtZero
-- name    : Kyprianou.Ch01.branchingOneAncestorLaplaceAtZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:30:11.126815+00:00
-- url     : https://prove2.me/theorems/36112e93-b41c-47fb-bc3d-d4fad48af532
-- title:
--   The initial single-ancestor population has the exact exponential Laplace transform
-- statement:
--   If the source one-ancestor branching law is initially the point mass at population one, then its exact source Laplace transform at time zero equals exp(-q), for every real discount parameter q. This is the starting identity for Exercise 1.11(iii) and its time-zero generator derivative.
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), worked answer p.306

import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorLaplaceAtZero
    (law : PopulationLaws) (hinit : law 1 0 = PMF.pure 1) (q : ℝ) :
    branchingLaplace law 1 0 q = Real.exp (-q) := by
  sorry
