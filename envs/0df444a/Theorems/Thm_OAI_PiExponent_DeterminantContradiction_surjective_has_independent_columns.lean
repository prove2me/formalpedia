-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_surjective_has_independent_columns
-- name    : OAI.PiExponent.DeterminantContradiction.surjective_has_independent_columns
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:24:07.975925+00:00
-- url     : https://prove2.me/theorems/4c74343a-1b7f-4443-8ef5-93ca9ab72ac8
-- title:
--   A surjective matrix has an independent selection of columns
-- statement:
--   If a finite matrix map is surjective, one can select an injectively indexed family of columns that is linearly independent. The argument extracts a basis from the finite spanning family of columns; for empty α, use the empty selection.

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

theorem OAI.PiExponent.DeterminantContradiction.surjective_has_independent_columns
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {K : Type*} [Field K] (A : Matrix α β K)
    (h : Function.Surjective A.mulVecLin) :
    ∃ selection : α → β,
      Function.Injective selection ∧
        LinearIndependent K (fun j : α => fun i : α => A i (selection j)) := by sorry
