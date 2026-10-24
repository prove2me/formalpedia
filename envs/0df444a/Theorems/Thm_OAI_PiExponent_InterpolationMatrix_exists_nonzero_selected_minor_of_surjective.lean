-- Prove2me | Theorems.Thm_OAI_PiExponent_InterpolationMatrix_exists_nonzero_selected_minor_of_surjective
-- name    : OAI.PiExponent.InterpolationMatrix.exists_nonzero_selected_minor_of_surjective
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:46:58.158257+00:00
-- url     : https://prove2.me/theorems/0a0c258a-62cd-4cce-a758-dd07b54dbd00
-- title:
--   A surjective finite matrix has a nonzero selected minor
-- statement:
--   For a finite matrix over Complex, surjectivity of its associated linear map gives an injective selection of one column for each row such that the resulting square minor has nonzero determinant.

import Mathlib
open scoped BigOperators

theorem OAI.PiExponent.InterpolationMatrix.exists_nonzero_selected_minor_of_surjective
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix α β Complex) (hM : Function.Surjective M.mulVecLin) :
    ∃ f : α → β, Function.Injective f ∧ (M.submatrix id f).det ≠ 0 := by sorry
