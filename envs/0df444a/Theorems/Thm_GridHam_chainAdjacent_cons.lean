-- Prove2me | Theorems.Thm_GridHam_chainAdjacent_cons
-- name    : GridHam.chainAdjacent_cons
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:29:17.307299+00:00
-- url     : https://prove2.me/theorems/07cc8bb7-5da2-436f-bcb1-ff623a51b35e
-- title:
--   Grid Ham: chain Adjacent cons
-- statement:
--   Prepending a vertex adjacent to the head keeps an adjacent-chain.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L464-L475
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L464-L475

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.chainAdjacent_cons (x y : Coord) (l : List Coord) (hh : l.head? = some y)
    (hadj : Adjacent x y) (hl : chainAdjacent l = true) : chainAdjacent (x :: l) = true := by sorry
