-- Prove2me | Theorems.Thm_GridHam_nodup_insert
-- name    : GridHam.nodup_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:57:50.326827+00:00
-- url     : https://prove2.me/theorems/877eeb75-5817-40b7-911b-8202a13f39fe
-- title:
--   Grid Ham: nodup insert
-- statement:
--   Inserting a `Nodup` list with no common elements between `a` and `b`
--   keeps `Nodup`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L717-L750
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L717-L750

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.nodup_insert (D : List Coord) (hD : D.Nodup) : ∀ (l1 : List Coord) (a b : Coord)
    (l2 : List Coord), (l1 ++ a :: b :: l2).Nodup → (∀ u ∈ D, u ∉ l1 ++ a :: b :: l2) →
    (l1 ++ a :: (D ++ b :: l2)).Nodup := by sorry
