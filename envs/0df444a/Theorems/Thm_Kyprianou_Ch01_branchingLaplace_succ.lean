-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingLaplace_succ
-- name    : Kyprianou.Ch01.branchingLaplace_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:22:01.207891+00:00
-- url     : https://prove2.me/theorems/dbcff204-afa6-4fcb-82ac-dd633b649af9
-- title:
--   Adding one ancestor multiplies branching Laplace transforms
-- statement:
--   The PMF branching convolution law implies factorisation of the exponential transform when adding one independent ancestor at positive Laplace frequency.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11(i), branching Laplace exponential theorem 25a9aaee-6e6e-4fb8-87d2-0c83e412f553; power law child 4ff5532f-a555-422c-9eea-5bd6e5cc2333.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingLaplace_succ
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (y : ℕ) (t : ℝ≥0) (phi : ℝ) (hphi : 0 < phi) :
    branchingLaplace law (y + 1) t phi =
      branchingLaplace law y t phi *
        branchingLaplace law 1 t phi := by sorry
