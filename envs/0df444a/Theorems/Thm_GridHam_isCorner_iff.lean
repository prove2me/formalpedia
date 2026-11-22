-- Prove2me | Theorems.Thm_GridHam_isCorner_iff
-- name    : GridHam.isCorner_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:53:06.036367+00:00
-- url     : https://prove2.me/theorems/c383d454-4f13-4609-8fe0-7af23cbc6f0a
-- title:
--   Grid Ham: is Corner iff
-- statement:
--   The Grid Ham construction uses the is Corner iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L82-L85
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L82-L85

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.isCorner_iff (w h x y : ℕ) : IsCorner w h (x, y) ↔ cornerA w h x y := by sorry
