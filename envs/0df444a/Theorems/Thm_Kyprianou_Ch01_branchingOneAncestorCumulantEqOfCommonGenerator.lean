-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorCumulantEqOfCommonGenerator
-- name    : Kyprianou.Ch01.branchingOneAncestorCumulantEqOfCommonGenerator
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T07:56:38.070703+00:00
-- url     : https://prove2.me/theorems/c2b1bbe1-e6c1-40c7-a688-9a9e7a522fdb
-- title:
--   Uniqueness of the positive-time branching cumulant ODE for matching offspring generators
-- statement:
--   For two branching Markov semigroups with common positive-rate Q-generator, identical pure point initial law and strictly positive and strictly subunit one-ancestor Laplace transforms, the logarithmic Laplace cumulants branchingU agree for every positive parameter and finite time. Use the already-Proved generator-to-Laplace derivative and semigroup-to-cumulant derivative results, then prove ODE uniqueness from local Lipschitz regularity of branchingMechanism on strictly positive cumulants without any finite offspring-moment assumption.
-- source:
--   Kyprianou (2006), Ch 1 §1.3.4 and Exercise 1.11: branching cumulant ODE and uniqueness in positive cumulant domain.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorCumulantEqOfCommonGenerator
    (rate : ℝ≥0) (hrate : 0 < rate) (offspring : PMF ℕ)
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
        0 < branchingLaplace K₂ 1 t q)
    (hBelow₁ : ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
        branchingLaplace K₁ 1 t q < 1)
    (hBelow₂ : ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
        branchingLaplace K₂ 1 t q < 1) :
    ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
      branchingU K₁ t q = branchingU K₂ t q := by
  sorry
