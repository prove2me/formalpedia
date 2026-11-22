-- Prove2me | Theorems.Thm_GridHam_nodup_map_of_injOn
-- name    : GridHam.nodup_map_of_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:50:47.016801+00:00
-- url     : https://prove2.me/theorems/ae5c5071-31dc-42a0-b546-201b80919988
-- title:
--   Grid Ham: nodup map of inj On
-- statement:
--   If `f` is injective on the elements of a `Nodup` list, the mapped list is
--   `Nodup`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L248-L266
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L248-L266

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.nodup_map_of_injOn (f : Coord → ℕ) : ∀ (l : List Coord),
    (∀ v ∈ l, ∀ w ∈ l, f v = f w → v = w) → l.Nodup → (l.map f).Nodup := by sorry
