-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingU_evolution_left_derivative
-- name    : Kyprianou.Ch01.branchingU_evolution_left_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:51:10.108447+00:00
-- url     : https://prove2.me/theorems/a0c51d99-cf24-498c-8b84-bf9756ac8ece
-- title:
--   Exercise 1.11(iii): branching cumulant left derivative at positive time
-- statement:
--   For each positive time, the branching cumulant has a left derivative equal to its branching mechanism. This is the outstanding interior-time smoothness bridge once the right derivative is known.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.11(iii); left differentiability required to combine one-sided derivatives of the cumulant.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingU_evolution_left_derivative
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
    (q : ℝ) (hq : 0 < q) (t : ℝ≥0) (ht : 0 < t) :
    HasDerivWithinAt
      (fun s : ℝ => branchingU law (Real.toNNReal s) q)
      (branchingMechanism rate offspring (branchingU law t q))
      (Set.Iic (t : ℝ)) (t : ℝ) := by sorry
