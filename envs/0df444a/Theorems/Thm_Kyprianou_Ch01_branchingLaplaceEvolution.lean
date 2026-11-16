-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingLaplaceEvolution
-- name    : Kyprianou.Ch01.branchingLaplaceEvolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:26:16.657843+00:00
-- url     : https://prove2.me/theorems/e3e56c90-ad7f-4e20-9c86-ac6cc59168cd
-- title:
--   Exercise 1.11(iii): Markov branching Laplace evolution equation
-- statement:
--   Kyprianou Exercise 1.11(iii): for a continuous-time Markov branching population with exponential lifetime rate λ>0 and offspring law, its one-ancestor cumulant u_t(q) satisfies u_0(q)=q and the right-time derivative ∂_t u_t(q)=ψ(u_t(q)), ψ(q)=λΣ_k p_k(1−e^{-q(k−1)}). Markov branching, initial one-ancestor law, positivity, and a first-order generator identity at t=0 are hypotheses. The evolution equation at all t is the independent conclusion; it is not an assumed ODE. Draft has not been remotely elaborated.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11(iii), printed p. 32; equation (1.18), printed p. 25.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingLaplaceEvolution
    (law : PopulationLaws)
    (rate : ℝ) (offspring : PMF ℕ)
    (hrate : 0 < rate)
    (hbranch : HasBranchingProperty law)
    (hsemigroup : IsPopulationMarkovSemigroup law)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hpositive : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
      0 < branchingLaplace law 1 t q ∧
        branchingLaplace law 1 t q < 1)
    (hgenerator : ∀ q : ℝ, 0 < q →
      HasDerivWithinAt
        (fun t : ℝ =>
          branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism rate offspring q) * Real.exp (-q))
        (Set.Ici 0) 0) :
    ∀ q : ℝ, 0 < q →
      branchingU law 0 q = q ∧
      ∀ t : ℝ≥0,
        HasDerivWithinAt
          (fun s : ℝ => branchingU law (Real.toNNReal s) q)
          (branchingMechanism rate offspring (branchingU law t q))
          (Set.Ici 0) (t : ℝ) := by
  sorry
