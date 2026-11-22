-- Prove2me | Theorems.Thm_GridHam_nodup_map_coord
-- name    : GridHam.nodup_map_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:42:15.998348+00:00
-- url     : https://prove2.me/theorems/92e09d9f-5f6a-48e2-90b5-0b008504c3bf
-- title:
--   Grid Ham: nodup map coord
-- statement:
--   Mapping an injective function preserves `Nodup`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L67-L83
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L67-L83

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.nodup_map_coord (f : Coord → Coord) (hf : ∀ v w, f v = f w → v = w) :
    ∀ (l : List Coord), l.Nodup → (l.map f).Nodup := by sorry
