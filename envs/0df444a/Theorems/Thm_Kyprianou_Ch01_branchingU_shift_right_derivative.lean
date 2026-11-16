-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingU_shift_right_derivative
-- name    : Kyprianou.Ch01.branchingU_shift_right_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:47:13.069055+00:00
-- url     : https://prove2.me/theorems/3c220f43-ec71-44ac-9327-3bc51f9d4a89
-- title:
--   Branching cumulant right derivative after any elapsed time
-- statement:
--   The derivative at zero of the time-shifted branching cumulant u↦U(t+u,q), taken over nonnegative increments, equals the branching mechanism evaluated at U(t,q). This follows from the cumulant semigroup property and the time-zero generator derivative.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11(iii); sound auxiliary for original nonlinear evolution derivative theorem cac5f39b-9e6c-49a1-9414-67383e408b9f.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingU_derivativeAtZero
import Theorems.Thm_Kyprianou_Ch01_branchingU_positive
import Theorems.Thm_Kyprianou_Ch01_branchingLaplaceSemigroup

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingU_shift_right_derivative
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
      (fun u : ℝ => branchingU law (t + Real.toNNReal u) q)
      (branchingMechanism rate offspring (branchingU law t q))
      (Set.Ici 0) 0 := by sorry
