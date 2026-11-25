-- Prove2me | Theorems.Thm_KirchhoffCayley_cauchy_binet
-- name    : KirchhoffCayley.cauchy_binet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:31:21.063645+00:00
-- url     : https://prove2.me/theorems/6604870c-8b79-41d9-bb22-378bf22e158d
-- title:
--   Kirchhoff Cayley: cauchy binet
-- statement:
--   **Cauchy–Binet formula.** `det (A * B) = ∑_{|S| = m} det A[·, S] * det B[S, ·]`, where the
--   columns of `A` and the rows of `B` indexed by `S` are taken in increasing order.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/Solution.lean#L30-L35
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/Solution.lean#L30-L35

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Definitions.Def_MatrixTree_Solution
public import Theorems.Thm_MatrixTree_cauchy_binet

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open KirchhoffCayley

theorem KirchhoffCayley.cauchy_binet {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) :
    (A * B).det = ∑ S : {S : Finset (Fin k) // S.card = m},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by sorry
