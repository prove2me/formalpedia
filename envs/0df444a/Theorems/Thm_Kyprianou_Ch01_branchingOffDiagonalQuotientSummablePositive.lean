-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOffDiagonalQuotientSummablePositive
-- name    : Kyprianou.Ch01.branchingOffDiagonalQuotientSummablePositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:10:25.564207+00:00
-- url     : https://prove2.me/theorems/8acceaea-b6d3-4b60-a4e7-310d2b085530
-- title:
--   Positive small-time off-diagonal quotient probabilities are nonnegative and summable
-- statement:
--   For any positive real time, the off-diagonal single-ancestor transition probabilities divided by elapsed time are nonnegative and summable, because the transition law is a probability mass function, the one diagonal term is set to zero, and division by a positive scalar preserves summability. This is the analytic admission condition for the discrete Scheffe lemma used in the textbook branching generator.
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), p.306

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOffDiagonalQuotientSummablePositive
    (law : PopulationLaws) (t : ℝ) (ht : 0 < t) :
    (∀ k : ℕ, 0 ≤
      (if k = 1 then (0 : ℝ)
       else ((law 1 (Real.toNNReal t)) k).toReal) / t) ∧
    Summable (fun k : ℕ =>
      (if k = 1 then (0 : ℝ)
       else ((law 1 (Real.toNNReal t)) k).toReal) / t) := by
  sorry
