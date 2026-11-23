-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorLaplaceEqPositiveRate
-- name    : Kyprianou.Ch01.branchingOneAncestorLaplaceEqPositiveRate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T07:46:59.973838+00:00
-- url     : https://prove2.me/theorems/e3cac5e7-a58d-4c85-b1bd-c04f5fbd4489
-- title:
--   Positive-rate uniqueness of one-ancestor Laplace evolutions with matching branching generators
-- statement:
--   For strictly positive life rate, two conservative branching Markov semigroups with identical initial laws, offspring generator, and positive Laplace transforms have identical one-ancestor Laplace transform for every positive parameter and time. Prove via common branching cumulant ODE and locally Lipschitz branching mechanism on positive cumulants without a finite offspring moment assumption.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, positive-rate branching cumulant ODE uniqueness, no finite offspring mean.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorLaplaceEqPositiveRate
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
        0 < branchingLaplace K₂ 1 t q) :
    ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
      branchingLaplace K₁ 1 t q = branchingLaplace K₂ 1 t q := by
  sorry
