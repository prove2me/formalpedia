-- Prove2me | Theorems.Thm_MatrixTree_det_eq_prod_diag_of_lt
-- name    : MatrixTree.det_eq_prod_diag_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:06:12.144085+00:00
-- url     : https://prove2.me/theorems/d13f8258-99e8-49f4-8a35-4dcd1fcfd91c
-- title:
--   Matrix Tree: det eq prod diag of lt
-- statement:
--   The Matrix Tree construction uses the det eq prod diag of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L172-L189
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L172-L189

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree

theorem MatrixTree.det_eq_prod_diag_of_lt {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (b : ι → ℕ) (h : ∀ i j, M i j ≠ 0 → i = j ∨ b i < b j) :
    M.det = ∏ i, M i i := by sorry
