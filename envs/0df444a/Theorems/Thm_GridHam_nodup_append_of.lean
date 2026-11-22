-- Prove2me | Theorems.Thm_GridHam_nodup_append_of
-- name    : GridHam.nodup_append_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:35:13.350313+00:00
-- url     : https://prove2.me/theorems/59238867-a868-4000-89f8-ea65a4c15472
-- title:
--   Grid Ham: nodup append of
-- statement:
--   Appending two lists with no common element preserves `Nodup`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L49-L64
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L49-L64

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.nodup_append_of : ∀ (l1 l2 : List Coord), l1.Nodup → l2.Nodup →
    (∀ v ∈ l1, ∀ w ∈ l2, v ≠ w) → (l1 ++ l2).Nodup := by sorry
