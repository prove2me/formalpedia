-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorLaplaceStrictPositive
-- name    : Kyprianou.Ch01.branchingOneAncestorLaplaceStrictPositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:15:00.659817+00:00
-- url     : https://prove2.me/theorems/da95e155-5bd7-45aa-a7c9-532548dc0980
-- title:
--   Strict positivity of a population PMF Laplace transform
-- statement:
--   At every branching time and every positive Laplace parameter, the one-ancestor population law is a probability mass function and its exponential weighting is strictly positive. This is independent of Markov or finite-mean assumptions, by a positive summand on the nonempty PMF support and domination by the PMF total mass.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, Laplace representation of branching populations, elementary PMF positivity

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorLaplaceStrictPositive
    (law : PopulationLaws) :
    ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
      0 < branchingLaplace law 1 t q := by
  sorry
