-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingLaplace_zero
-- name    : Kyprianou.Ch01.branchingLaplace_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:22:08.565195+00:00
-- url     : https://prove2.me/theorems/e58c638f-924b-45e9-90de-a92ef42fb7b9
-- title:
--   With zero ancestors the branching Laplace transform is one
-- statement:
--   The Laplace transform of the zero-ancestor pure-zero law is one at any time and frequency.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11(i), branching Laplace exponential theorem 25a9aaee-6e6e-4fb8-87d2-0c83e412f553; power law child 4ff5532f-a555-422c-9eea-5bd6e5cc2333.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingLaplace_zero
    (law : PopulationLaws)
    (hzero : ∀ t : ℝ≥0, law 0 t = PMF.pure 0)
    (t : ℝ≥0) (phi : ℝ) :
    branchingLaplace law 0 t phi = 1 := by sorry
