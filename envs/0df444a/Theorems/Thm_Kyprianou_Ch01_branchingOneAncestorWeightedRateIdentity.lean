-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorWeightedRateIdentity
-- name    : Kyprianou.Ch01.branchingOneAncestorWeightedRateIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:27:48.472637+00:00
-- url     : https://prove2.me/theorems/a28155cc-a558-461d-87fb-452204f94206
-- title:
--   One-ancestor branching WeightedRateIdentity
-- statement:
--   The source offspring distribution has p_1=0. Thus the row-one branching Q-matrix has diagonal -lambda and off-diagonal lambda p_k, and its exponentially weighted sum is exactly the negative source branching mechanism times exp(-q). The proof needs the PMF normalisation and absolute summability, and explicitly preserves the no-null-jumps condition.
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), worked answer printed page 306

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorWeightedRateIdentity
    (rate : ℝ≥0) (offspring : PMF ℕ)
    (hNoNullJumps : offspring 1 = 0)
    (q : ℝ) (hq : 0 < q) :
    (∑' k : ℕ,
      (if k = 1 then -(rate : ℝ)
       else (rate : ℝ) * (offspring k).toReal) *
      Real.exp (-q * (k : ℝ))) =
      -(branchingMechanism (rate : ℝ) offspring q) *
        Real.exp (-q) := by
  sorry
