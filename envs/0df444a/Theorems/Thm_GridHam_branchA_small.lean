-- Prove2me | Theorems.Thm_GridHam_branchA_small
-- name    : GridHam.branchA_small
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:05:16.975531+00:00
-- url     : https://prove2.me/theorems/28e43b35-b8f7-4e98-8140-2b1172493eee
-- title:
--   Grid Ham: branch A small
-- statement:
--   The Grid Ham construction uses the branch A small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L301-L306
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L301-L306

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxRecDepth 100000

theorem GridHam.branchA_small : ∀ w ∈ List.range 6, 4 ≤ w → ∀ h ∈ List.range (w + 1), NotPrime w h →
    ∀ sx ∈ List.range w, ∀ sy ∈ List.range h, ∀ tx ∈ List.range w, ∀ ty ∈ List.range h,
    ¬ (sx = tx ∧ sy = ty) → sx ≤ tx →
    AccA w h sx sy tx ty → 2 ≤ sx →
    AccA (w - 2) h (sx - 2) sy (tx - 2) ty ∧ FreeCol 2 h sx sy tx ty := by sorry
