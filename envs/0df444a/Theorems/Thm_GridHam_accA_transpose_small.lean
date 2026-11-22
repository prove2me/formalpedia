-- Prove2me | Theorems.Thm_GridHam_accA_transpose_small
-- name    : GridHam.accA_transpose_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:04:39.750832+00:00
-- url     : https://prove2.me/theorems/358fed7e-f6f6-4317-a2e9-0be9fa6ccc2a
-- title:
--   Grid Ham: acc A transpose small
-- statement:
--   The Grid Ham construction uses the acc A transpose small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L193-L196
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L193-L196

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxRecDepth 100000

theorem GridHam.accA_transpose_small : ∀ w ∈ List.range 4, ∀ h ∈ List.range 4, ∀ sx ∈ List.range w,
    ∀ sy ∈ List.range h, ∀ tx ∈ List.range w, ∀ ty ∈ List.range h,
    (AccA w h sx sy tx ty ↔ AccA h w sy sx ty tx) := by sorry
