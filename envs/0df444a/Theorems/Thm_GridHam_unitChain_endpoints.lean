-- Prove2me | Theorems.Thm_GridHam_unitChain_endpoints
-- name    : GridHam.unitChain_endpoints
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:50:42.810951+00:00
-- url     : https://prove2.me/theorems/51cb8c6e-c905-4652-9053-fccd2ff974e1
-- title:
--   Grid Ham: unit Chain endpoints
-- statement:
--   A `Nodup` unit-step chain covering exactly `[k, k + rest.length]` runs
--   from one end of that range to the other.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L235-L242
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L235-L242

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.unitChain_endpoints (a : ℕ) (rest : List ℕ) (k : ℕ)
    (hnd : (a :: rest).Nodup) (hch : unitStepChain (a :: rest) = true)
    (hcov : ∀ y, y ∈ a :: rest ↔ k ≤ y ∧ y ≤ k + rest.length) :
    (a = k ∧ (a :: rest).getLast? = some (k + rest.length)) ∨
    (a = k + rest.length ∧ (a :: rest).getLast? = some k) := by sorry
