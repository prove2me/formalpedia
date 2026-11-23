-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingCumulantFiniteHorizonRegular
-- name    : Kyprianou.Ch01.branchingCumulantFiniteHorizonRegular
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:39:54.466452+00:00
-- url     : https://prove2.me/theorems/4f22e404-4cee-4cf5-a491-bb05dfb2fab5
-- title:
--   Positive continuous branching cumulant solution of its finite-horizon ODE
-- statement:
--   Given the original one-ancestor branching-property, Markov semigroup, point mass at zero, and branching rate generator with positive rate and no neutral offspring, and positive subunit Laplace transform for each positive q, the logarithmic cumulant is continuous and strictly positive over every finite nonnegative time interval and satisfies the branching mechanism ODE with right derivatives. Reuse the already Proved branchingOneAncestorGeneratorFromRates, branchingU_timeContinuous, branchingU_positive, branchingU_evolution_derivative. No finite offspring moment assumption.
-- source:
--   Kyprianou (2006), Chapter 1 section 1.3.4, using existing Proved Kyprianou.Ch01 branching cumulant trajectory results.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingCumulantFiniteHorizonRegular
    (rate : ℝ≥0) (hrate : 0 < rate) (offspring : PMF ℕ)
    (hNoZeroJumps : offspring 1 = 0)
    (K : PopulationLaws)
    (hBranch : HasBranchingProperty K)
    (hSemi : IsPopulationMarkovSemigroup K)
    (hInit : ∀ y : ℕ, K y 0 = PMF.pure y)
    (hGen : IsBranchingRateGenerator K rate offspring)
    (hPos : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
       0 < branchingLaplace K 1 t q)
    (hBelow : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
       branchingLaplace K 1 t q < 1)
    (T : ℝ≥0) (q : ℝ) (hq : 0 < q) :
    let f : ℝ → ℝ := fun s => branchingU K (Real.toNNReal s) q
    ContinuousOn f (Set.Icc 0 (T : ℝ)) ∧
    (∀ s ∈ Set.Icc 0 (T : ℝ), 0 < f s) ∧
    (∀ s ∈ Set.Ico 0 (T : ℝ),
      HasDerivWithinAt f
        (branchingMechanism (rate : ℝ) offspring (f s))
        (Set.Ici s) s) := by
  sorry
