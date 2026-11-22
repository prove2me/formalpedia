-- Prove2me | Theorems.Thm_GridHam_chainAdjacent_replace_tail
-- name    : GridHam.chainAdjacent_replace_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:10.504054+00:00
-- url     : https://prove2.me/theorems/e4524882-5397-48d2-8dcd-f3ad6a57e166
-- title:
--   Grid Ham: chain Adjacent replace tail
-- statement:
--   Replacing everything after `a` by another chain that starts at `a`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L662-L691
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L662-L691

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.chainAdjacent_replace_tail : ∀ (l1 : List Coord) (a : Coord) (m m' : List Coord),
    chainAdjacent (l1 ++ a :: m) = true → chainAdjacent (a :: m') = true →
    chainAdjacent (l1 ++ a :: m') = true := by sorry
