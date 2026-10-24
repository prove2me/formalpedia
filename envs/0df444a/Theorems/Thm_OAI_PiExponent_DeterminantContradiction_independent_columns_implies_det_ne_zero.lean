-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_independent_columns_implies_det_ne_zero
-- name    : OAI.PiExponent.DeterminantContradiction.independent_columns_implies_det_ne_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:24:19.144098+00:00
-- url     : https://prove2.me/theorems/5efb0449-17c9-40f6-99f9-417b8357ead9
-- title:
--   Independent columns give a nonzero determinant
-- statement:
--   For a square matrix over a field, linear independence of its columns implies that its determinant is nonzero. Column independence gives injectivity of the associated endomorphism; finite dimensionality gives invertibility, which is equivalent to a nonzero determinant. The empty square matrix is covered by the same criterion.

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

theorem OAI.PiExponent.DeterminantContradiction.independent_columns_implies_det_ne_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    {K : Type*} [Field K] (M : Matrix α α K)
    (h : LinearIndependent K (fun j : α => fun i : α => M i j)) :
    M.det ≠ 0 := by sorry
