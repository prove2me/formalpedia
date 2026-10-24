-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_exists_nonzero_selected_minor_of_surjective_actualMatrix
-- name    : OAI.PiExponent.DeterminantContradiction.exists_nonzero_selected_minor_of_surjective_actualMatrix
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T16:56:38.27696+00:00
-- url     : https://prove2.me/theorems/08fbd546-9e92-4e74-9f5a-3b0adeec6eeb
-- title:
--   Surjectivity of a finite complex matrix yields a nonzero selected minor
-- statement:
--   A surjective finite complex matrix has an injective choice of one column per row whose square submatrix has nonzero determinant.

import Mathlib
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.exists_nonzero_selected_minor_of_surjective_actualMatrix
    {alpha beta : Type*} [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (M : Matrix alpha beta Complex) (hM : Function.Surjective M.mulVecLin) :
    ∃ f : alpha → beta, Function.Injective f ∧ (M.submatrix id f).det ≠ 0 := by sorry
