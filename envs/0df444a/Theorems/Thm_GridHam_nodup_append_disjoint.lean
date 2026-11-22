-- Prove2me | Theorems.Thm_GridHam_nodup_append_disjoint
-- name    : GridHam.nodup_append_disjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:47:18.683486+00:00
-- url     : https://prove2.me/theorems/a63c9b0b-8014-4965-89bc-08156c64835a
-- title:
--   Grid Ham: nodup append disjoint
-- statement:
--   The Grid Ham construction uses the nodup append disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L254-L266
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L254-L266

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.nodup_append_disjoint : ∀ (l1 l2 : List Coord), (l1 ++ l2).Nodup →
    ∀ c ∈ l1, c ∉ l2 := by sorry
