-- Prove2me | Theorems.Thm_MatrixTree_matrix_tree
-- name    : MatrixTree.matrix_tree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:56:10.088202+00:00
-- url     : https://prove2.me/theorems/de1ce40b-3d5e-4b66-8dff-3be414982924
-- title:
--   Matrix Tree: matrix tree
-- statement:
--   **Kirchhoff's matrix-tree theorem.** The number of spanning trees of a finite graph is the
--   determinant of its Laplacian with the row and column of any vertex removed.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L383-L475
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L383-L475

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree

theorem MatrixTree.matrix_tree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    (Nat.card {H : SimpleGraph V // H ≤ G ∧ H.IsTree} : ℤ) =
      ((G.lapMatrix ℤ).submatrix (Subtype.val : {u // u ≠ v} → V) Subtype.val).det := by sorry
