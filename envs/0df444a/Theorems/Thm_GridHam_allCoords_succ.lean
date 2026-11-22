-- Prove2me | Theorems.Thm_GridHam_allCoords_succ
-- name    : GridHam.allCoords_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:25:26.770347+00:00
-- url     : https://prove2.me/theorems/50243647-6c57-4a65-94d5-2a9e1ed10088
-- title:
--   Grid Ham: all Coords succ
-- statement:
--   The Grid Ham construction uses the all Coords succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L244-L246
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L244-L246

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.allCoords_succ (w h : ℕ) :
    allCoords (w + 1) h = allCoords w h ++ (List.range h).map (fun y => (w, y)) := by sorry
