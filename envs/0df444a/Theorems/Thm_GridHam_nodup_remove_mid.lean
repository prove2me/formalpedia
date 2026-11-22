-- Prove2me | Theorems.Thm_GridHam_nodup_remove_mid
-- name    : GridHam.nodup_remove_mid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:10:05.33714+00:00
-- url     : https://prove2.me/theorems/6c32c740-6347-46ae-a131-2414a4544341
-- title:
--   Grid Ham: nodup remove mid
-- statement:
--   The Grid Ham construction uses the nodup remove mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L536-L571
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L536-L571

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.nodup_remove_mid : ∀ (L : List Coord) (a b : Coord) (M R : List Coord),
    (L ++ a :: (M ++ b :: R)).Nodup →
    (L ++ a :: b :: R).Nodup ∧ ∀ c ∈ M, c ∉ L ++ a :: b :: R := by sorry
