-- Prove2me | Theorems.Thm_GridHam_unitChain_head_extreme
-- name    : GridHam.unitChain_head_extreme
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:49:46.227316+00:00
-- url     : https://prove2.me/theorems/f94927ce-5294-4ebc-97dc-65881bed4ec7
-- title:
--   Grid Ham: unit Chain head extreme
-- statement:
--   In a `Nodup` unit-step chain covering exactly `[k, k + rest.length]`,
--   the first element is one of the two ends of that range. An interior first
--   element `a` would have both `a - 1` and `a + 1` later in the list, so by
--   `unitStepChain_intermediate` `a` itself would appear later too --
--   contradicting `Nodup`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L109-L140
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L109-L140

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.unitChain_head_extreme (a : ℕ) (rest : List ℕ) (k : ℕ)
    (hnd : (a :: rest).Nodup) (hch : unitStepChain (a :: rest) = true)
    (hcov : ∀ y, y ∈ a :: rest ↔ k ≤ y ∧ y ≤ k + rest.length) :
    a = k ∨ a = k + rest.length := by sorry
