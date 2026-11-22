-- Prove2me | Theorems.Thm_Lean4LPD_tZero_anti
-- name    : Lean4LPD.tZero_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:04:02.197165+00:00
-- url     : https://prove2.me/theorems/0278a896-550a-4ae7-b013-dc37d5360844
-- title:
--   Lean4 LPD: t Zero anti
-- statement:
--   **`t₀` is antitone in `c₀`**: for `0 < c ≤ c'` (and `0 < G`, `1 < kh`, `0 < a`),
--   `tZero c' G kh a ≤ tZero c G kh a`. Hence an upper bound on `c₀` is a lower bound on the threshold
--   `t₀`, and replacing `c₀` by a larger constant `c'` shrinks the guaranteed time window `t < t₀` by
--   the factor `c'/c₀`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L325-L338
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L325-L338

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.tZero_anti {c c' G kh a : ℝ} (hc : 0 < c) (hcc : c ≤ c') (hG : 0 < G) (hkh : 1 < kh)
    (ha : 0 < a) : tZero c' G kh a ≤ tZero c G kh a := by sorry
