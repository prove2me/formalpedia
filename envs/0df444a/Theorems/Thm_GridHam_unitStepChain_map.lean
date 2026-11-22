-- Prove2me | Theorems.Thm_GridHam_unitStepChain_map
-- name    : GridHam.unitStepChain_map
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:50:51.505716+00:00
-- url     : https://prove2.me/theorems/9090f0f2-e820-43c2-b846-23ee07df3570
-- title:
--   Grid Ham: unit Step Chain map
-- statement:
--   If every grid-adjacent pair of elements maps to values differing by 1,
--   a grid-adjacent chain maps to a unit-step chain.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L270-L297
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L270-L297

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.unitStepChain_map (f : Coord → ℕ) : ∀ (l : List Coord),
    (∀ v ∈ l, ∀ w ∈ l, Adjacent v w → (f v + 1 = f w ∨ f w + 1 = f v)) →
    chainAdjacent l = true → unitStepChain (l.map f) = true := by sorry
