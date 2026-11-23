-- Prove2me | Theorems.Thm_Kyprianou_Ch01_oneAncestorDiagonalSupermultiplicative
-- name    : Kyprianou.Ch01.oneAncestorDiagonalSupermultiplicative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:03:02.666902+00:00
-- url     : https://prove2.me/theorems/123d3809-443e-4805-b684-4f6472ea25f5
-- title:
--   One-ancestor return probability is supermultiplicative in time for a population Markov semigroup
-- statement:
--   For a semigroup of population transition PMFs, the probability of starting at one and returning to one after s+t dominates the product of the two one-to-one transition probabilities. Apply Chapman-Kolmogorov at initial state one, expand PMF.bind at final state one, and retain the nonnegative n=1 summand of the ENNReal series. No branching or finite-mean assumption is necessary.
-- source:
--   Markov Chapman-Kolmogorov semigroup identity in Kyprianou (2006), Chapter 1 §1.3.4.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.oneAncestorDiagonalSupermultiplicative
    (law : PopulationLaws)
    (hSemi : IsPopulationMarkovSemigroup law)
    (s t : ℝ≥0) :
    (law 1 s 1) * (law 1 t 1) ≤ law 1 (s + t) 1 := by
  sorry
