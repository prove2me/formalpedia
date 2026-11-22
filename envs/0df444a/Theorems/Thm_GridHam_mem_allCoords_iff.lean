-- Prove2me | Theorems.Thm_GridHam_mem_allCoords_iff
-- name    : GridHam.mem_allCoords_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:23:55.560096+00:00
-- url     : https://prove2.me/theorems/516e2f0c-47a1-4bfe-9912-b55e1e979efc
-- title:
--   Grid Ham: mem all Coords iff
-- statement:
--   The Grid Ham construction uses the mem all Coords iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L181-L188
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L181-L188

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.mem_allCoords_iff (w h : ℕ) (v : Coord) :
    v ∈ allCoords w h ↔ v.1 < w ∧ v.2 < h := by sorry
