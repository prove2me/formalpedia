-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingLaplaceMarkovFactorization
-- name    : Kyprianou.Ch01.branchingLaplaceMarkovFactorization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:33:02.49585+00:00
-- url     : https://prove2.me/theorems/e6bfb731-e761-49d2-810c-17430b6110e4
-- title:
--   Kyprianou Exercise 1.11(ii): branching Markov Laplace-transform composition
-- statement:
--   For a branching Markov population semigroup with positive one-ancestor Laplace transforms, the one-ancestor transform over s+t is the one-ancestor transform over s evaluated at the branching cumulant U(t,phi). This is the exact Laplace-transform step behind the composition law U(s+t,phi)=U(s,U(t,phi)).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.11(ii), original semigroup target 28390140-9324-491d-9840-2083bcf0ad34.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingLaplaceMarkovFactorization
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hmarkov : IsPopulationMarkovSemigroup law)
    (hzero : ∀ t : ℝ≥0, law 0 t = PMF.pure 0)
    (hpositive : ∀ t : ℝ≥0, ∀ phi : ℝ, 0 < phi →
      0 < branchingLaplace law 1 t phi ∧
        branchingLaplace law 1 t phi < 1) :
    ∀ (s t : ℝ≥0) (phi : ℝ), 0 < phi →
      branchingLaplace law 1 (s + t) phi =
        branchingLaplace law 1 s (branchingU law t phi) := by sorry
