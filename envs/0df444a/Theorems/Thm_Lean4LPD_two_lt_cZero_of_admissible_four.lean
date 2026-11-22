-- Prove2me | Theorems.Thm_Lean4LPD_two_lt_cZero_of_admissible_four
-- name    : Lean4LPD.two_lt_cZero_of_admissible_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:03:53.179357+00:00
-- url     : https://prove2.me/theorems/76579926-582b-4008-8c61-991468f64a82
-- title:
--   Lean4 LPD: two lt c Zero of admissible four
-- statement:
--   **The hypothesis `5 ≤ r` of `cZero_le_two` cannot be weakened to `4 ≤ r`.** At
--   `(r, m*, Γ, B) = (4, 1, 8, 1)` every other hypothesis holds — the triple is admissible, since
--   `8(m*+1)² = 32 ≤ 4·8 = rΓ`, and `1 ≤ m`, `0 ≤ B ≤ 1` — and
--   `c₀ = (5/4)·exp(9/64)·√2 ≈ 2.035 > 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L277-L297
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L277-L297

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.two_lt_cZero_of_admissible_four :
    Admissible 4 1 8 ∧ 2 < cZero 4 1 8 1 := by sorry
