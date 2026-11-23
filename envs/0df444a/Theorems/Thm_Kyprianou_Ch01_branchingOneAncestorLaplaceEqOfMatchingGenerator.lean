-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorLaplaceEqOfMatchingGenerator
-- name    : Kyprianou.Ch01.branchingOneAncestorLaplaceEqOfMatchingGenerator
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T07:16:39.898742+00:00
-- url     : https://prove2.me/theorems/2b6295c5-a4ca-4322-8027-bf38d013fc6c
-- title:
--   Equality of one-ancestor Laplace flows from a common branching generator
-- statement:
--   Two conservative population branching semigroups with the same initial point masses and the same offspring Q-generator, with strictly positive one-ancestor Laplace transforms, have identical Laplace flow at every positive parameter and time. Establish the Markov branching composition evolution, positivity/strict unit upper bounds and uniqueness of its nonlinear cumulant ODE without requiring finite offspring mean.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, branching semigroup Laplace flow and generator uniqueness

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorLaplaceEqOfMatchingGenerator
    (rate : ℝ≥0) (offspring : PMF ℕ)
    (hNoZeroJumps : offspring 1 = 0)
    (K₁ K₂ : PopulationLaws)
    (hBranch₁ : HasBranchingProperty K₁)
    (hBranch₂ : HasBranchingProperty K₂)
    (hSemi₁ : IsPopulationMarkovSemigroup K₁)
    (hSemi₂ : IsPopulationMarkovSemigroup K₂)
    (hInit₁ : ∀ y : ℕ, K₁ y 0 = PMF.pure y)
    (hInit₂ : ∀ y : ℕ, K₂ y 0 = PMF.pure y)
    (hGen₁ : IsBranchingRateGenerator K₁ rate offspring)
    (hGen₂ : IsBranchingRateGenerator K₂ rate offspring)
    (hPos₁ : ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
        0 < branchingLaplace K₁ 1 t q)
    (hPos₂ : ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
        0 < branchingLaplace K₂ 1 t q) :
    ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
      branchingLaplace K₁ 1 t q = branchingLaplace K₂ 1 t q := by
  sorry
