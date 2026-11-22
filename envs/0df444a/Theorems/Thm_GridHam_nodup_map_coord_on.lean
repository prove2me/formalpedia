-- Prove2me | Theorems.Thm_GridHam_nodup_map_coord_on
-- name    : GridHam.nodup_map_coord_on
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:40:51.764845+00:00
-- url     : https://prove2.me/theorems/69947cce-2d4a-471f-80bc-ddff2b7135b5
-- title:
--   Grid Ham: nodup map coord on
-- statement:
--   The Grid Ham construction uses the nodup map coord on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L1009-L1027
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L1009-L1027

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.nodup_map_coord_on (f : Coord → Coord) : ∀ (l : List Coord),
    (∀ v ∈ l, ∀ u ∈ l, f v = f u → v = u) → l.Nodup → (l.map f).Nodup := by sorry
