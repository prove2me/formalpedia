-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_exists_injective_selected_columns_of_surjective_actualMatrix
-- name    : OAI.PiExponent.DeterminantContradiction.exists_injective_selected_columns_of_surjective_actualMatrix
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:00:52.263101+00:00
-- url     : https://prove2.me/theorems/b8e98e83-3928-4e08-95b0-f0e508ef331a
-- title:
--   Extract independent columns from a surjective matrix
-- statement:
--   If the matrix map is surjective, its columns contain a linearly independent subfamily indexed injectively by the row type.

import Mathlib
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.exists_injective_selected_columns_of_surjective_actualMatrix
    {alpha beta : Type*} [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (M : Matrix alpha beta Complex) (hM : Function.Surjective M.mulVecLin) :
    ∃ f : alpha → beta, Function.Injective f ∧
      LinearIndependent Complex (fun i => M.col (f i)) := by sorry
