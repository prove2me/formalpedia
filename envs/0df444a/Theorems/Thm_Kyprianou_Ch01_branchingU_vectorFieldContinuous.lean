-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingU_vectorFieldContinuous
-- name    : Kyprianou.Ch01.branchingU_vectorFieldContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T18:00:35.495603+00:00
-- url     : https://prove2.me/theorems/b10827bf-f1d7-428a-981a-b9f87f6a9a63
-- title:
--   Continuous branching mechanism evaluated along the time-continuous positive cumulant
-- statement:
--   Assuming the established time continuity of the cumulant along with the same branching hypotheses and positive Laplace parameter, its composition with the branching mechanism is a continuous real-valued function. This requires continuity of the PMF-weighted branching mechanism for positive cumulant arguments.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.11(iii), branching mechanism continuity obligation

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingU_vectorFieldContinuous
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
    (q : ℝ) (hq : 0 < q)
    (hUcont : ContinuousOn
      (fun s : ℝ => branchingU law (Real.toNNReal s) q)
      (Set.Ici 0)) :
    Continuous
      (fun s : ℝ => branchingMechanism rate offspring
        (branchingU law (Real.toNNReal s) q)) := by sorry
