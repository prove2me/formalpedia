-- Prove2me | Theorems.Thm_Lean4LPD_cZero_le_two_of_three_le_m
-- name    : Lean4LPD.cZero_le_two_of_three_le_m
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:04:24.18861+00:00
-- url     : https://prove2.me/theorems/336a81bd-63bb-40ae-837e-b0578d44655b
-- title:
--   Lean4 LPD: c Zero le two of three le m
-- statement:
--   **`m* ≥ 3` gives `c₀ ≤ 2`** on `Admissible r m G` with `0 ≤ B ≤ 1` — no further condition on
--   `r`, none on `Γ`.
--
--   Each factor is bounded separately from `m* ≥ 3`, which is why this needs none of the machinery the
--   `Γ` route did: `m ≤ r` gives `r ≥ 3` so `(r+1)/r ≤ 4/3`; `8(m*+1)² ≤ rΓ` caps the exponent at
--   `9/(32(m*+1)) ≤ 9/128`; and `m* + 1 ≥ 4` caps the root at `2^{1/4}`. The product is `1.7210`, a
--   **13.9%** margin — against 0.81% for `Γ ≤ 7`, so this is much the sturdiest of the three conditions.
--
--   **Cost in step count.** `Admissible`'s `8(m*+1)² ≤ rΓ` ties `m*` to `r`: raising `m*` to 3 raises
--   the step floor to `r ≥ 128/Γ`, which at `Γ_eff = 6` is `r ≥ 21.3`, about four times the floor of
--   the `r ≥ 5` route at the same `Γ`. The hypothesis itself constrains no Trotter parameter; through
--   `Admissible` its margin is paid for in step count.
--
--   **Three is the least sufficient integer, but not the threshold over ℝ.** `Admissible` quantifies
--   `m : ℝ`, and numerically the threshold is `m* = 2.14237…`, the root of
--   `(1+1/m)·e^{9/(32(m+1))}·2^{1/(m+1)} = 2`. So `m* ≥ 9/4` would also suffice (supremum `1.9494`);
--   these real thresholds are numerical observations and are not formalized. The integer `3` is stated
--   because `m*` is a rung index, an integer in the paper, not because the bound fails just below it.
--   `two_lt_cZero_of_m_two` shows `m* ≥ 2` does not suffice, so no integer smaller than 3 works.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L538-L570
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L538-L570

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.cZero_le_two_of_three_le_m {r m G B : ℝ} (h : Admissible r m G) (hm3 : 3 ≤ m)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 2 := by sorry
