-- Prove2me | Theorems.Thm_MatrixTree_det_mul_eq_sum_fun
-- name    : MatrixTree.det_mul_eq_sum_fun
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T11:01:02.963087+00:00
-- url     : https://prove2.me/theorems/dfd3c3f0-69ed-54db-ad13-184b512c983d
-- title:
--   Matrix Tree: det mul eq sum fun
-- statement:
--   The Matrix Tree construction uses the det mul eq sum fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L32-L38
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L32-L38

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree

theorem MatrixTree.det_mul_eq_sum_fun {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) :
    (A * B).det = ∑ p : Fin m → Fin k, (A.submatrix id p).det * ∏ i, B (p i) i := by sorry
