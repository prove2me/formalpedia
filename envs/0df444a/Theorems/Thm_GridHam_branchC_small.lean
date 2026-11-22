-- Prove2me | Theorems.Thm_GridHam_branchC_small
-- name    : GridHam.branchC_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:04:47.147977+00:00
-- url     : https://prove2.me/theorems/8f7abb33-4836-4edf-81c8-eafcca413a69
-- title:
--   Grid Ham: branch C small
-- statement:
--   The Grid Ham construction uses the branch C small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L350-L355
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L350-L355

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxRecDepth 100000

theorem GridHam.branchC_small : ∀ w ∈ List.range 6, 4 ≤ w → ∀ h ∈ List.range (w + 1), NotPrime w h →
    ∀ sx ∈ List.range w, ∀ sy ∈ List.range h, ∀ tx ∈ List.range w, ∀ ty ∈ List.range h,
    ¬ (sx = tx ∧ sy = ty) → sx ≤ tx →
    AccA w h sx sy tx ty → sx ≤ 1 → tx + 2 < w →
    AccA (w - 2) h sx sy tx ty ∧ FreeCol (w - 3) h sx sy tx ty := by sorry
