-- Prove2me | Theorems.Thm_GridHam_freeCol_exists
-- name    : GridHam.freeCol_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:15:53.208928+00:00
-- url     : https://prove2.me/theorems/3621e585-b160-4dee-a703-61e30cfad558
-- title:
--   Grid Ham: free Col exists
-- statement:
--   A free vertex in column `c`, in the form the strip lemmas want.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Main.lean#L41-L53
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Main.lean#L41-L53

module
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_Reduction
public import Definitions.Def_GridHam_Necessity
public import Definitions.Def_GridHam_Main
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.freeCol_exists (c h sx sy tx ty : ℕ) (hf : FreeCol c h sx sy tx ty) :
    ∃ y, y < h ∧ (c, y) ≠ (sx, sy) ∧ (c, y) ≠ (tx, ty) := by sorry
