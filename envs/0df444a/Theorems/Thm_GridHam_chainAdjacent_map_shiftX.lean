-- Prove2me | Theorems.Thm_GridHam_chainAdjacent_map_shiftX
-- name    : GridHam.chainAdjacent_map_shiftX
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:54:05.91935+00:00
-- url     : https://prove2.me/theorems/2006c064-e133-4289-9f5a-2070a6e9fbe8
-- title:
--   Grid Ham: chain Adjacent map shift X
-- statement:
--   Shifting preserves grid adjacency along a chain.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L86-L111
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L86-L111

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.chainAdjacent_map_shiftX (d : ℕ) : ∀ (l : List Coord),
    chainAdjacent l = true → chainAdjacent (l.map (shiftX d)) = true := by sorry
