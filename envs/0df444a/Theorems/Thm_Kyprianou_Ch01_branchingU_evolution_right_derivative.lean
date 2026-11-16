-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingU_evolution_right_derivative
-- name    : Kyprianou.Ch01.branchingU_evolution_right_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:51:06.652939+00:00
-- url     : https://prove2.me/theorems/80abc1ae-f371-4a2e-9258-4af9bbf0ad9f
-- title:
--   Exercise 1.11(iii): branching cumulant right derivative in physical time
-- statement:
--   For each nonnegative time t, the branching cumulant has the right derivative equal to its branching mechanism. This converts the proved shifted-time right derivative to the actual process time variable.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.11(iii); derived from the proved shifted right derivative 3c220f43-ec71-44ac-9327-3bc51f9d4a89.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingU_evolution_right_derivative
    (law : PopulationLaws)
    (rate : ℝ) (offspring : PMF ℕ)
    (hbranch : HasBranchingProperty law)
    (hsemigroup : IsPopulationMarkovSemigroup law)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hpositive : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
      0 < branchingLaplace law 1 t q ∧
        branchingLaplace law 1 t q < 1)
    (hgenerator : ∀ q : ℝ, 0 < q →
      HasDerivWithinAt
        (fun t : ℝ => branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism rate offspring q) * Real.exp (-q))
        (Set.Ici 0) 0)
    (q : ℝ) (hq : 0 < q) (t : ℝ≥0) :
    HasDerivWithinAt
      (fun s : ℝ => branchingU law (Real.toNNReal s) q)
      (branchingMechanism rate offspring (branchingU law t q))
      (Set.Ici (t : ℝ)) (t : ℝ) := by sorry
