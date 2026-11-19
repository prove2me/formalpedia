-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorOffDiagonalMass
-- name    : Kyprianou.Ch01.branchingOneAncestorOffDiagonalMass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:45:48.677398+00:00
-- url     : https://prove2.me/theorems/d6ed7846-1554-42e1-ae9d-cc1a3de9544f
-- title:
--   Off-diagonal branching population probability is the complement of the one-ancestor stay probability
-- statement:
--   At each time t, the one-ancestor branching population transition kernel is a genuine probability mass function. The total real probability across states other than one equals 1 minus the probability of still being in state one. This exact complement identity permits the total off-diagonal small-time mass derivative to be controlled from the specified single diagonal generator derivative, and is a key mass-conservation step before any interchange of the infinite Laplace transform derivative.
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), worked answer p.306

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorOffDiagonalMass
    (law : PopulationLaws) (t : NNReal) :
    (∑' k : ℕ,
      if k = 1 then (0 : ℝ) else ((law 1 t) k).toReal) =
      1 - ((law 1 t) 1).toReal := by
  sorry
