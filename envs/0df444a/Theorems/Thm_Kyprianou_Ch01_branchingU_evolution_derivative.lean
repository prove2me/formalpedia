-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingU_evolution_derivative
-- name    : Kyprianou.Ch01.branchingU_evolution_derivative
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T21:39:14.59324+00:00
-- url     : https://prove2.me/theorems/cac5f39b-9e6c-49a1-9414-5cf630a1ca3a
-- title:
--   Kyprianou Exercise 1.11(iii): branching cumulant nonlinear evolution equation
-- statement:
--   Under the exact Markov branching, time-zero identity, positivity and generator-derivative hypotheses, the cumulant U(t,q) solves its nonlinear branching-mechanism evolution equation on the nonnegative time half-line. This is the differential part of the original Exercise 1.11(iii).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.11(iii), source theorem e3e56c90-ad7f-4e20-9c86-ac6cc59168cd.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingU_evolution_derivative
    (law : PopulationLaws)
    (rate : ℝ) (offspring : PMF ℕ)
    (hrate : 0 < rate)
    (hbranch : HasBranchingProperty law)
    (hsemigroup : IsPopulationMarkovSemigroup law)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hpositive : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
      0 < branchingLaplace law 1 t q ∧
        branchingLaplace law 1 t q < 1)
    (hgenerator : ∀ q : ℝ, 0 < q →
      HasDerivWithinAt
        (fun t : ℝ =>
          branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism rate offspring q) * Real.exp (-q))
        (Set.Ici 0) 0) :
    ∀ q : ℝ, 0 < q →
      ∀ t : ℝ≥0,
        HasDerivWithinAt
          (fun s : ℝ => branchingU law (Real.toNNReal s) q)
          (branchingMechanism rate offspring (branchingU law t q))
          (Set.Ici 0) (t : ℝ) := by sorry
