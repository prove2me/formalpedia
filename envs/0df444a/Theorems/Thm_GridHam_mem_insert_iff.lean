-- Prove2me | Theorems.Thm_GridHam_mem_insert_iff
-- name    : GridHam.mem_insert_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:29:58.27823+00:00
-- url     : https://prove2.me/theorems/685cd300-9462-4d1b-b117-cd7f9a53385f
-- title:
--   Grid Ham: mem insert iff
-- statement:
--   The Grid Ham construction uses the mem insert iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L710-L713
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L710-L713

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.mem_insert_iff (u : Coord) (l1 D l2 : List Coord) (a b : Coord) :
    u ∈ l1 ++ a :: (D ++ b :: l2) ↔ u ∈ D ∨ u ∈ l1 ++ a :: b :: l2 := by sorry
