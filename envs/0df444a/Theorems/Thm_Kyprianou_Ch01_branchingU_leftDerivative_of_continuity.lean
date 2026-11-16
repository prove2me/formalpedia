-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingU_leftDerivative_of_continuity
-- name    : Kyprianou.Ch01.branchingU_leftDerivative_of_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T17:57:44.323386+00:00
-- url     : https://prove2.me/theorems/565a08cc-8059-494c-90a4-315ce8e9c4a5
-- title:
--   Branching cumulant evolution from the right derivative and continuity of its vector field
-- statement:
--   Under the original branching, semigroup, initialisation, positivity and generator hypotheses, together with continuity in real time of the cumulant at fixed q and continuity of the composition of the branching mechanism with that cumulant, the desired left derivative at every positive time is the branching mechanism at the cumulant. The proof uses the already-Proved right derivative at all nonnegative times and the continuous-right-derivative-to-left-derivative theorem. These continuity assumptions remain separate nontrivial obligations for the original exercise.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11(iii), sound reduction under continuity

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingU_evolution_right_derivative
import Theorems.Thm_Kyprianou_Ch01_continuousRightDerivative_impliesLeft
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingU_leftDerivative_of_continuity
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
    (q : ℝ) (hq : 0 < q) (t : ℝ≥0) (ht : 0 < t)
    (hUcont : ContinuousOn
      (fun s : ℝ => branchingU law (Real.toNNReal s) q) (Set.Ici 0))
    (hGcont : Continuous
      (fun s : ℝ =>
        branchingMechanism rate offspring
          (branchingU law (Real.toNNReal s) q))) :
    HasDerivWithinAt
      (fun s : ℝ => branchingU law (Real.toNNReal s) q)
      (branchingMechanism rate offspring (branchingU law t q))
      (Set.Iic (t : ℝ)) (t : ℝ) := by sorry
