-- Prove2me | Theorems.Thm_MatrixTree_sum_perm_eq_det
-- name    : MatrixTree.sum_perm_eq_det
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T11:01:31.731204+00:00
-- url     : https://prove2.me/theorems/fd218d51-efd2-456d-8520-e53c1308aa29
-- title:
--   Matrix Tree: sum perm eq det
-- statement:
--   The Matrix Tree construction uses the sum perm eq det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L47-L55
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L47-L55

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree

theorem MatrixTree.sum_perm_eq_det {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) (e : Fin m → Fin k) :
    ∑ τ : Equiv.Perm (Fin m), (A.submatrix id (e ∘ τ)).det * ∏ i, B (e (τ i)) i =
      (A.submatrix id e).det * (B.submatrix e id).det := by sorry
