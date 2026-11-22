-- Prove2me | Theorems.Thm_GridHam_branchB_small
-- name    : GridHam.branchB_small
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:06:05.517352+00:00
-- url     : https://prove2.me/theorems/6c901f69-c338-4209-9d2f-26e0d90fd858
-- title:
--   Grid Ham: branch B small
-- statement:
--   The Grid Ham construction uses the branch B small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L413-L418
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L413-L418

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxRecDepth 100000

theorem GridHam.branchB_small : ∀ w ∈ List.range 6, 4 ≤ w → ∀ h ∈ List.range (w + 1), NotPrime w h →
    ∀ sx ∈ List.range w, ∀ sy ∈ List.range h, ∀ tx ∈ List.range w, ∀ ty ∈ List.range h,
    ¬ (sx = tx ∧ sy = ty) → sx ≤ tx →
    AccA w h sx sy tx ty → sx ≤ 1 → w ≤ tx + 2 →
    BConcl w h sx sy tx ty (rChoice sx sy h) := by sorry
