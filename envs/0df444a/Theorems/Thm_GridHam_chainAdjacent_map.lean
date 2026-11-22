-- Prove2me | Theorems.Thm_GridHam_chainAdjacent_map
-- name    : GridHam.chainAdjacent_map
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:54:36.808946+00:00
-- url     : https://prove2.me/theorems/28ed627b-c901-46cd-9142-97d1f7bafffb
-- title:
--   Grid Ham: chain Adjacent map
-- statement:
--   Any map that preserves adjacency preserves adjacent-chains.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L292-L316
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L292-L316

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.chainAdjacent_map (f : Coord → Coord) (hf : ∀ v w, Adjacent v w → Adjacent (f v) (f w)) :
    ∀ (l : List Coord), chainAdjacent l = true → chainAdjacent (l.map f) = true := by sorry
