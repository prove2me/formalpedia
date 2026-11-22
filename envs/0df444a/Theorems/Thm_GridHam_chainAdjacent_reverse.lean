-- Prove2me | Theorems.Thm_GridHam_chainAdjacent_reverse
-- name    : GridHam.chainAdjacent_reverse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:37:38.840851+00:00
-- url     : https://prove2.me/theorems/30281ac7-3266-4c76-95a9-7d9e402331f0
-- title:
--   Grid Ham: chain Adjacent reverse
-- statement:
--   Reversing an adjacent-chain gives an adjacent-chain.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L319-L339
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L319-L339

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.chainAdjacent_reverse : ∀ (l : List Coord),
    chainAdjacent l = true → chainAdjacent l.reverse = true := by sorry
