-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingCumulantODEUniqueOfLocallyLipschitzMechanism
-- name    : Kyprianou.Ch01.branchingCumulantODEUniqueOfLocallyLipschitzMechanism
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:17:14.454797+00:00
-- url     : https://prove2.me/theorems/a2ce8794-4155-483a-a894-aacfe9658289
-- title:
--   Positive branching cumulant ODE uniqueness assuming local Lipschitz mechanism
-- statement:
--   With the original matched generator, branching, semigroup, initial value, positive and subunit Laplace assumptions, plus local Lipschitz regularity of the true branching vector field on positive compact intervals, both cumulant processes solve the same autonomous ODE u prime equals mechanism(u) with the same initial value. Reuse already Proved branchingOneAncestorGeneratorFromRates, branchingU_timeContinuous, branchingU_evolution_derivative and local solution uniqueness. The explicit local Lipschitz premise is supplied by the other child without offspring moment restriction.
-- source:
--   Kyprianou (2006), Chapter 1 section 1.3.4; pinned Mathlib ODE uniqueness and Proved chapter generator-to-cumulant derivatives.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingCumulantODEUniqueOfLocallyLipschitzMechanism
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
        branchingLaplace K₂ 1 t q < 1)
    (hLip : ∀ (a b : ℝ), 0 < a → a ≤ b →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
          |branchingMechanism (rate : ℝ) offspring y -
            branchingMechanism (rate : ℝ) offspring x| ≤
            C * |y - x|) :
    ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
      branchingU K₁ t q = branchingU K₂ t q := by
  sorry
