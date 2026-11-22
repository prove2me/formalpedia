-- Prove2me | Theorems.Thm_Lean4LPD_two_lt_cZero_of_m_zero
-- name    : Lean4LPD.two_lt_cZero_of_m_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:03:58.585672+00:00
-- url     : https://prove2.me/theorems/5a8f5b53-0dc7-41e2-9ba8-7ae2375e8043
-- title:
--   Lean4 LPD: two lt c Zero of m zero
-- statement:
--   **The hypothesis `1 ≤ m` of `cZero_le_two` cannot be dropped.** At
--   `(r, m*, Γ, B) = (5, 0, 2, 1)` every other hypothesis holds — `r ≥ m*` reads `5 ≥ 0`,
--   `8(m*+1)² = 8 ≤ 5·2 = rΓ`, `5 ≤ r` and `0 ≤ B ≤ 1` — yet
--
--     `c₀ = (6/5)·exp(9/40)·(1+1)^{1/1} ≈ 3.006 > 2`,
--
--   because at `m* = 0` the root exponent `1/(m*+1)` is `1`, so the entry factor `1 + B` enters
--   undiluted. The middle conjunct `(5 : ℝ) ≥ 5` records that `5 ≤ r` holds at the witness.
--   `two_lt_cZero_of_m_zero_general` extends this to every `r` and `Γ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L308-L319
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L308-L319

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.two_lt_cZero_of_m_zero : Admissible 5 0 2 ∧ (5 : ℝ) ≥ 5 ∧ 2 < cZero 5 0 2 1 := by sorry
