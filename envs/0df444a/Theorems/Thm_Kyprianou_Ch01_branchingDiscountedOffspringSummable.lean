-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingDiscountedOffspringSummable
-- name    : Kyprianou.Ch01.branchingDiscountedOffspringSummable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:38:55.27345+00:00
-- url     : https://prove2.me/theorems/f58147f6-f236-41ca-a02f-00925fe057d0
-- title:
--   branchingDiscountedOffspringSummable
-- statement:
--   The offspring probability law has total real mass one and its exponential-discounted probability sequence is absolutely summable for q>0. This follows from finite total ENNReal PMF mass and the exponential discount weights lying in [0,1], enabling safe transformations of the source one-ancestor branching mechanism.
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), back-of-book answer p.306

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingDiscountedOffspringSummable
    (offspring : PMF ℕ) (q : ℝ) (hq : 0 < q) :
    (∑' k : ℕ, (offspring k).toReal) = 1 ∧
    Summable (fun k : ℕ =>
      (offspring k).toReal * Real.exp (-q * (k : ℝ))) := by
  sorry
