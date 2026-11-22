-- Prove2me | Theorems.Thm_GridHam_exists_col_edge
-- name    : GridHam.exists_col_edge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:57:00.473655+00:00
-- url     : https://prove2.me/theorems/63f67d59-3a24-40c4-956e-4829b5e0753e
-- title:
--   Grid Ham: exists col edge
-- statement:
--   **Degree argument.** In an adjacent-chain with no repeats lying in
--   columns `≤ X`, any vertex in column `X` that is neither the first nor the
--   last element has a neighbour on the chain in the same column (its two chain
--   neighbours are distinct, and only one can be its left neighbour). So the
--   chain contains two consecutive vertices in column `X`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L569-L640
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L569-L640

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.exists_col_edge (X : ℕ) : ∀ (l : List Coord), chainAdjacent l = true → l.Nodup →
    (∀ u ∈ l, u.1 ≤ X) → ∀ v ∈ l, v.1 = X → l.head? ≠ some v → l.getLast? ≠ some v →
    ∃ l1 a b l2, l = l1 ++ a :: b :: l2 ∧ a.1 = X ∧ b.1 = X := by sorry
