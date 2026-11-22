-- Prove2me | Theorems.Thm_GridHam_nodup_not_mem_last
-- name    : GridHam.nodup_not_mem_last
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:48:08.818125+00:00
-- url     : https://prove2.me/theorems/ad261c94-c02f-4beb-978b-3e2097624668
-- title:
--   Grid Ham: nodup not mem last
-- statement:
--   The Grid Ham construction uses the nodup not mem last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L104-L117
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L104-L117

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.nodup_not_mem_last : ∀ (m : List Coord) (t : Coord), (m ++ [t]).Nodup → t ∉ m := by sorry
