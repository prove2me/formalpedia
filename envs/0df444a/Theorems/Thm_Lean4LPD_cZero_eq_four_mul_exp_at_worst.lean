-- Prove2me | Theorems.Thm_Lean4LPD_cZero_eq_four_mul_exp_at_worst
-- name    : Lean4LPD.cZero_eq_four_mul_exp_at_worst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:04:32.564799+00:00
-- url     : https://prove2.me/theorems/760e5a9c-ab66-4f9c-9f0a-978421927009
-- title:
--   Lean4 LPD: c Zero eq four mul exp at worst
-- statement:
--   **`4e^{9/32}` is attained**, so `cZero_le_four_mul_exp` is sharp and no smaller unconditional
--   constant exists. `(1, 0, 8)` is admissible with `8(m*+1)² = 8 = 1·8` holding with equality, and
--   every one of the three factor bounds is tight there at once, so `4e^{9/32} ≈ 5.2991` is the
--   **maximum** of `c₀` over `Admissible` and `0 ≤ B ≤ 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L671-L678
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L671-L678

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.cZero_eq_four_mul_exp_at_worst :
    Admissible 1 0 8 ∧ cZero 1 0 8 1 = 4 * exp (9 / 32) := by sorry
