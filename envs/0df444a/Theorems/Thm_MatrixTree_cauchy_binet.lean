-- Prove2me | Theorems.Thm_MatrixTree_cauchy_binet
-- name    : MatrixTree.cauchy_binet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:56:03.832251+00:00
-- url     : https://prove2.me/theorems/6246d8a5-4001-50ff-90a3-cb6ef65efe43
-- title:
--   Matrix Tree: cauchy binet
-- statement:
--   **Cauchy–Binet formula.** `det (A * B) = ∑_{|S| = m} det A[·, S] * det B[S, ·]`, where the
--   columns of `A` and the rows of `B` indexed by `S` are taken in increasing order.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L59-L113
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L59-L113

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree

theorem MatrixTree.cauchy_binet {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) :
    (A * B).det = ∑ S : {S : Finset (Fin k) // S.card = m},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by sorry
