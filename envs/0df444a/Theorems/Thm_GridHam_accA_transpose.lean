-- Prove2me | Theorems.Thm_GridHam_accA_transpose
-- name    : GridHam.accA_transpose
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:04:11.415989+00:00
-- url     : https://prove2.me/theorems/567cc2f6-01fa-4eab-bd0a-6a746b050406
-- title:
--   Grid Ham: acc A transpose
-- statement:
--   Acceptability is invariant under transposing the grid.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L233-L262
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L233-L262

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxHeartbeats 2000000

theorem GridHam.accA_transpose (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h) :
    AccA w h sx sy tx ty ↔ AccA h w sy sx ty tx := by sorry
