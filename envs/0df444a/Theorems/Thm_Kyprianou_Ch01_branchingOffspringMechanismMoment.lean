-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOffspringMechanismMoment
-- name    : Kyprianou.Ch01.branchingOffspringMechanismMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:38:59.90257+00:00
-- url     : https://prove2.me/theorems/9d3ee094-57cd-4987-9968-0392fca18937
-- title:
--   branchingOffspringMechanismMoment
-- statement:
--   The source branching mechanism's offspring expectation is one minus the discounted offspring exponential moment rescaled by exp(q), using PMF real mass one, summability and the exact identity exp(-q*(k-1))=exp(q)*exp(-q*k). This is independent of the Q-row diagonal computation.
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), back-of-book answer p.306

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOffspringMechanismMoment
    (offspring : PMF ℕ) (q : ℝ) (hq : 0 < q) :
    (∑' k : ℕ,
      (offspring k).toReal *
        (1 - Real.exp (-q * ((k : ℝ) - 1)))) =
      1 - Real.exp q *
        (∑' k : ℕ,
          (offspring k).toReal * Real.exp (-q * (k : ℝ))) := by
  sorry
