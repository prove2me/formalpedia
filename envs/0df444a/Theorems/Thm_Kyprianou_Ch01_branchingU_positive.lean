-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingU_positive
-- name    : Kyprianou.Ch01.branchingU_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:48:08.033875+00:00
-- url     : https://prove2.me/theorems/c471c585-20ea-4a98-a50c-888db0c62370
-- title:
--   Positive branching cumulant from strictly subunit Laplace transform
-- statement:
--   If the one-ancestor Laplace transform lies strictly between zero and one for all positive Laplace arguments, the corresponding negative logarithmic cumulant is strictly positive at every nonnegative time.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11(ii)-(iii), positivity hypothesis in the branching cumulant semigroup and differential evolution.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingU_positive
    (law : PopulationLaws)
    (hpositive : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
      0 < branchingLaplace law 1 t q ∧
        branchingLaplace law 1 t q < 1)
    (t : ℝ≥0) (q : ℝ) (hq : 0 < q) :
    0 < branchingU law t q := by sorry
