-- Prove2me | Theorems.Thm_GridHam_unitChain_last_of_head_max
-- name    : GridHam.unitChain_last_of_head_max
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:50:22.705969+00:00
-- url     : https://prove2.me/theorems/645eefb8-4b18-452e-9c5a-b887fc7fef90
-- title:
--   Grid Ham: unit Chain last of head max
-- statement:
--   Mirror image of `unitChain_last_of_head_min`: starting at the top
--   `k + rest.length` forces ending at the bottom `k`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L191-L231
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L191-L231

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.unitChain_last_of_head_max :
    ∀ (rest : List ℕ) (a k : ℕ), (a :: rest).Nodup → unitStepChain (a :: rest) = true →
      (∀ y, y ∈ a :: rest ↔ k ≤ y ∧ y ≤ k + rest.length) → a = k + rest.length →
      (a :: rest).getLast? = some k := by sorry
