-- Prove2me | Theorems.Thm_Lean4LPD_two_lt_cZero_of_m_two
-- name    : Lean4LPD.two_lt_cZero_of_m_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:04:27.006282+00:00
-- url     : https://prove2.me/theorems/d7c8e490-8033-431e-9016-6674ede348a0
-- title:
--   Lean4 LPD: two lt c Zero of m two
-- statement:
--   **`m* ≥ 2` does not suffice**, so the `3` of `cZero_le_two_of_three_le_m` is the least
--   sufficient integer. `(r, m*, Γ, B) = (2, 2, 36, 1)` is admissible — `m ≤ r` reads `2 ≤ 2` and
--   `8(m*+1)² = 72 = 2·36` holds with equality — and
--
--     `c₀ = (3/2)·e^{3/32}·2^{1/3} ≈ 2.0756`,
--
--   3.8% above 2. This point is moreover the **maximizer** of `c₀` at `m* = 2`, `B = 1` over the
--   admissible set: both constraints on `r` are active, `r = max(1, m*) = 2` and
--   `Γ = 8(m*+1)²/r = 36`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L581-L597
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L581-L597

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.two_lt_cZero_of_m_two : Admissible 2 2 36 ∧ 2 < cZero 2 2 36 1 := by sorry
