-- Prove2me | Theorems.Thm_KirchhoffCayley_matrix_tree
-- name    : KirchhoffCayley.matrix_tree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:54:31.585911+00:00
-- url     : https://prove2.me/theorems/632ff374-76b8-523d-af1c-89e56e921de0
-- title:
--   Kirchhoff Cayley: matrix tree
-- statement:
--   **Kirchhoff's matrix-tree theorem.** The number of spanning trees of a finite graph is the
--   determinant of its Laplacian with the row and column of any vertex removed.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/Solution.lean#L39-L43
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/Solution.lean#L39-L43

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Definitions.Def_MatrixTree_Solution
public import Theorems.Thm_MatrixTree_matrix_tree

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open KirchhoffCayley

theorem KirchhoffCayley.matrix_tree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    (Nat.card {H : SimpleGraph V // H ≤ G ∧ H.IsTree} : ℤ) =
      ((G.lapMatrix ℤ).submatrix (Subtype.val : {u // u ≠ v} → V) Subtype.val).det := by sorry
