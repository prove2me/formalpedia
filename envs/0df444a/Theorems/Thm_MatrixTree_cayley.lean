-- Prove2me | Theorems.Thm_MatrixTree_cayley
-- name    : MatrixTree.cayley
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:01:02.008226+00:00
-- url     : https://prove2.me/theorems/7441ce9f-ca0e-4414-aef4-863b1906667b
-- title:
--   Matrix Tree: cayley
-- statement:
--   **Cayley's formula.** For `n ≥ 1` there are `n ^ (n - 2)` trees on `Fin n`.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L532-L551
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L532-L551

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree

theorem MatrixTree.cayley (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) := by sorry
