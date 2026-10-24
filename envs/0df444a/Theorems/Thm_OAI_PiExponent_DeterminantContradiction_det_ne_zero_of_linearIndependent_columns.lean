-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_det_ne_zero_of_linearIndependent_columns
-- name    : OAI.PiExponent.DeterminantContradiction.det_ne_zero_of_linearIndependent_columns
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:01:15.057994+00:00
-- url     : https://prove2.me/theorems/15dcc162-2be3-403a-957c-c973395090d5
-- title:
--   Independent columns give nonzero determinant
-- statement:
--   A square complex matrix with linearly independent columns has nonzero determinant.

import Mathlib
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.det_ne_zero_of_linearIndependent_columns
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (A : Matrix alpha alpha Complex)
    (hA : LinearIndependent Complex A.col) : A.det ≠ 0 := by sorry
