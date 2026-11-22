-- Prove2me | Theorems.Thm_GridHam_chainAdjacent_append
-- name    : GridHam.chainAdjacent_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:35:46.835971+00:00
-- url     : https://prove2.me/theorems/6dd0728c-9f02-40b8-b749-1a9f477e45da
-- title:
--   Grid Ham: chain Adjacent append
-- statement:
--   Two adjacent-chains joined by an adjacent pair form an adjacent-chain.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L114-L143
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L114-L143

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.chainAdjacent_append : ∀ (l1 : List Coord) (b : Coord) (l2 : List Coord) (a : Coord),
    l1.getLast? = some a → chainAdjacent l1 = true → Adjacent a b →
    chainAdjacent (b :: l2) = true → chainAdjacent (l1 ++ b :: l2) = true := by sorry
