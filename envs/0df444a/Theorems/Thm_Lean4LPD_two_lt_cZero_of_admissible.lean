-- Prove2me | Theorems.Thm_Lean4LPD_two_lt_cZero_of_admissible
-- name    : Lean4LPD.two_lt_cZero_of_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:03:44.308889+00:00
-- url     : https://prove2.me/theorems/06d13987-0c77-465c-b478-ce4701b22e7e
-- title:
--   Lean4 LPD: two lt c Zero of admissible
-- statement:
--   **The hypothesis `5 ≤ r` of `cZero_le_two` cannot be dropped, even at `B = 0`.** The triple
--   `(r, m*, Γ) = (1, 1, 32)` is admissible — `r ≥ m*` reads `1 ≥ 1`, and
--   `8(m*+1)² = 32 ≤ 1 · 32 = rΓ` — it satisfies `1 ≤ m`, and at `B = 0` it gives
--   `c₀ = 2·exp(9/64) ≈ 2.302 > 2`.
--
--   `B = 0` is the most favourable value of the entry factor, so no improvement of the entry-factor
--   bound can give `c₀ ≤ 2` from `Admissible` and `1 ≤ m` alone. `scripts/c0_scan.py` evaluates the
--   same point numerically.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L260-L271
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L260-L271

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.two_lt_cZero_of_admissible :
    Admissible 1 1 32 ∧ 2 < cZero 1 1 32 0 := by sorry
