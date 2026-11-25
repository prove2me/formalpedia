-- Prove2me | Theorems.Thm_KirchhoffCayley_cayley
-- name    : KirchhoffCayley.cayley
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:00:05.324586+00:00
-- url     : https://prove2.me/theorems/9f60e80a-84ef-4621-a18b-f3cca1bba264
-- title:
--   Kirchhoff Cayley: cayley
-- statement:
--   **Cayley's formula.** For `n ≥ 1` there are `n ^ (n - 2)` trees on `Fin n`.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/Solution.lean#L46-L48
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/Solution.lean#L46-L48

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Definitions.Def_MatrixTree_Solution
public import Theorems.Thm_MatrixTree_cayley

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open KirchhoffCayley

theorem KirchhoffCayley.cayley (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) := by sorry
