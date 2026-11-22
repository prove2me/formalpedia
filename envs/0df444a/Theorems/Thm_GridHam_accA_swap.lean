-- Prove2me | Theorems.Thm_GridHam_accA_swap
-- name    : GridHam.accA_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:03:22.450431+00:00
-- url     : https://prove2.me/theorems/d2d338c2-27c7-4ed7-a379-d3bdb0b1142e
-- title:
--   Grid Ham: acc A swap
-- statement:
--   Acceptability does not depend on which endpoint is called `s`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L200-L229
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L200-L229

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxHeartbeats 2000000

theorem GridHam.accA_swap (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h) :
    AccA w h sx sy tx ty ↔ AccA w h tx ty sx sy := by sorry
