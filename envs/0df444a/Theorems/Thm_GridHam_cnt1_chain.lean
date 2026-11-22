-- Prove2me | Theorems.Thm_GridHam_cnt1_chain
-- name    : GridHam.cnt1_chain
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:24:09.897134+00:00
-- url     : https://prove2.me/theorems/18172670-ba1b-4e6e-bce7-191b101555c6
-- title:
--   Grid Ham: cnt1 chain
-- statement:
--   Colours alternate along an adjacent-chain, so a chain starting at `a` with
--   `l.length + 1` cells has `(l.length + 1 + parity a) / 2` cells of colour 1.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L204-L227
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L204-L227

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.cnt1_chain : ∀ (l : List Coord) (a : Coord), chainAdjacent (a :: l) = true →
    cnt1 (a :: l) = (l.length + 1 + parity a) / 2 := by sorry
