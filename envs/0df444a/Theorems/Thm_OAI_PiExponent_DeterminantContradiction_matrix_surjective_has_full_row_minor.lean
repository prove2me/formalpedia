-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_matrix_surjective_has_full_row_minor
-- name    : OAI.PiExponent.DeterminantContradiction.matrix_surjective_has_full_row_minor
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:20:19.234993+00:00
-- url     : https://prove2.me/theorems/b917c162-bd76-423b-8b6c-b71f4d416cd0
-- title:
--   A surjective finite matrix has a nonsingular full-row minor
-- statement:
--   For a finite matrix over a field, surjectivity of its matrix linear map implies there is an injective choice of one column for each row whose resulting square submatrix has nonzero determinant. The statement includes the empty-row case.

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

theorem OAI.PiExponent.DeterminantContradiction.matrix_surjective_has_full_row_minor
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {𝕜 : Type*} [Field 𝕜] (A : Matrix α β 𝕜)
    (h : Function.Surjective A.mulVecLin) :
    ∃ selection : α → β,
      Function.Injective selection ∧ (A.submatrix id selection).det ≠ 0 := by sorry
