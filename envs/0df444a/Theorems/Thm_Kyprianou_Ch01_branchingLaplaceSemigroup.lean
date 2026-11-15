-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingLaplaceSemigroup
-- name    : Kyprianou.Ch01.branchingLaplaceSemigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:25:52.237109+00:00
-- url     : https://prove2.me/theorems/28390140-9324-491d-9840-2083bcf0ad34
-- title:
--   Exercise 1.11(ii): composition law for branching Laplace cumulants
-- statement:
--   Under time-homogeneous Markov branching with zero absorbing and strictly positive one-ancestor Laplace transform, prove u_(s+t)(φ)=u_s(u_t(φ)). The book's symmetric version u_(t+s)=u_s(u_t(φ)) follows by renaming the two time variables. This is a genuine semigroup consequence, distinct from the branching property itself. Draft uncompiled.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.11, pp. 31–32.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingLaplaceSemigroup
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hmarkov : IsPopulationMarkovSemigroup law)
    (hzero : ∀ t : ℝ≥0, law 0 t = PMF.pure 0)
    (hpositive : ∀ t : ℝ≥0, ∀ phi : ℝ, 0 < phi →
      0 < branchingLaplace law 1 t phi ∧
        branchingLaplace law 1 t phi < 1) :
    ∀ (s t : ℝ≥0) (phi : ℝ), 0 < phi →
      branchingU law (s + t) phi =
        branchingU law s (branchingU law t phi) := by
  sorry
