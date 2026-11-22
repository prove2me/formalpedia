-- Prove2me | Theorems.Thm_GridHam_cnt1_cons
-- name    : GridHam.cnt1_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:24:12.431909+00:00
-- url     : https://prove2.me/theorems/26f0c306-9d1a-4cd3-ad90-d35498e7aadb
-- title:
--   Grid Ham: cnt1 cons
-- statement:
--   The Grid Ham construction uses the cnt1 cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L193-L196
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L193-L196

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.cnt1_cons (a : Coord) (l : List Coord) :
    cnt1 (a :: l) = cnt1 l + (if parity a = 1 then 1 else 0) := by sorry
