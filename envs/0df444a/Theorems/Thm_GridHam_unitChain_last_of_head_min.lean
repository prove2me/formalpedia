-- Prove2me | Theorems.Thm_GridHam_unitChain_last_of_head_min
-- name    : GridHam.unitChain_last_of_head_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:50:12.772548+00:00
-- url     : https://prove2.me/theorems/148e9354-6516-4808-a846-d4fb0cf35fb7
-- title:
--   Grid Ham: unit Chain last of head min
-- statement:
--   A `Nodup` unit-step chain covering `[k, k + rest.length]` that starts at
--   the bottom `k` ends at the top. The second element is forced to be `k + 1`,
--   and the tail covers `[k + 1, k + 1 + rest'.length]`; induct.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L145-L187
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L145-L187

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.unitChain_last_of_head_min :
    ∀ (rest : List ℕ) (a k : ℕ), (a :: rest).Nodup → unitStepChain (a :: rest) = true →
      (∀ y, y ∈ a :: rest ↔ k ≤ y ∧ y ≤ k + rest.length) → a = k →
      (a :: rest).getLast? = some (k + rest.length) := by sorry
