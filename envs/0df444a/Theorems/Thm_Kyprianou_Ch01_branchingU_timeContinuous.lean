-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingU_timeContinuous
-- name    : Kyprianou.Ch01.branchingU_timeContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T18:00:38.21834+00:00
-- url     : https://prove2.me/theorems/a5ffb5a9-889d-43a7-a599-7bac8cb79394
-- title:
--   Time continuity of one-ancestor branching cumulants under their Markov semigroup and generator
-- statement:
--   Under the branching, Markov semigroup, initialisation, positivity and infinitesimal-generator hypotheses of Exercise 1.11(iii), the one-ancestor log-Laplace cumulant is continuous in nonnegative physical time for every positive Laplace parameter.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.11(iii), semigroup time-continuity obligation

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingU_timeContinuous
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
    (q : ℝ) (hq : 0 < q):
    ContinuousOn
      (fun s : ℝ => branchingU law (Real.toNNReal s) q)
      (Set.Ici 0) := by sorry
