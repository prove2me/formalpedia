-- Prove2me | Theorems.Thm_GridHam_pnext_adj
-- name    : GridHam.pnext_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:31:36.808796+00:00
-- url     : https://prove2.me/theorems/24071c93-de93-4e77-b22f-75c110293542
-- title:
--   Grid Ham: pnext adj
-- statement:
--   The Grid Ham construction uses the pnext adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L46-L55
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L46-L55

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.pnext_adj {p : List Coord} {x y : Coord} (hch : chainAdjacent p = true)
    (h : PNext p x y) : Adjacent x y := by sorry
