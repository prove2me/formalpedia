-- Prove2me | Theorems.Thm_MatrixTree_det_submatrix_eq_zero_of_not_injective
-- name    : MatrixTree.det_submatrix_eq_zero_of_not_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T11:01:14.913795+00:00
-- url     : https://prove2.me/theorems/bc94f2fe-9b82-4e5e-bb9f-fc5d05d3787c
-- title:
--   Matrix Tree: det submatrix eq zero of not injective
-- statement:
--   The Matrix Tree construction uses the det submatrix eq zero of not injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L40-L45
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L40-L45

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree

theorem MatrixTree.det_submatrix_eq_zero_of_not_injective {R : Type*} [CommRing R] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) R) (p : Fin m → Fin k) (hp : ¬ Function.Injective p) :
    (A.submatrix id p).det = 0 := by sorry
