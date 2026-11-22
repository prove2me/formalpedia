-- Prove2me | Theorems.Thm_GridHam_chainAdjacent_tail
-- name    : GridHam.chainAdjacent_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:37:53.394226+00:00
-- url     : https://prove2.me/theorems/ac30ccf8-fc01-4d9e-95cb-ee2cc2546a4c
-- title:
--   Grid Ham: chain Adjacent tail
-- statement:
--   The Grid Ham construction uses the chain Adjacent tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L644-L652
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L644-L652

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.chainAdjacent_tail (x : Coord) (L : List Coord) (h : chainAdjacent (x :: L) = true) :
    chainAdjacent L = true := by sorry
