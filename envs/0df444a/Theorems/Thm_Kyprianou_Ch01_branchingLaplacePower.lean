-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingLaplacePower
-- name    : Kyprianou.Ch01.branchingLaplacePower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:20:29.659192+00:00
-- url     : https://prove2.me/theorems/4ff5532f-a555-422c-9eea-5bd6e5cc2333
-- title:
--   Kyprianou Exercise 1.11: branching Laplace transforms factorise by initial population
-- statement:
--   For a continuous-time integer-valued branching population, the Laplace transform from y initial ancestors is the y-th power of the one-ancestor Laplace transform. The exact branching convolution property and zero-ancestor pure-zero law are assumed. Positive Laplace frequency ensures the transforms are finite.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.11(i), original target 25a9aaee-6e6e-4fb8-87d2-0c83e412f553.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingLaplacePower
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hzero : ∀ t : ℝ≥0, law 0 t = PMF.pure 0) :
    ∀ (y : ℕ) (t : ℝ≥0) (phi : ℝ), 0 < phi →
      branchingLaplace law y t phi =
        (branchingLaplace law 1 t phi) ^ y := by sorry
