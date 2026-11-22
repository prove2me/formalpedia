-- Prove2me | Theorems.Thm_Lean4LPD_cZero_le_four_mul_exp
-- name    : Lean4LPD.cZero_le_four_mul_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:04:32.873448+00:00
-- url     : https://prove2.me/theorems/78c3234a-a0d3-4074-95ae-030cd1b9417f
-- title:
--   Lean4 LPD: c Zero le four mul exp
-- statement:
--   **The sharp unconditional bound: `c₀ ≤ 4e^{9/32} ≈ 5.2991`**, on `Admissible` and
--   `0 ≤ B ≤ 1` alone — no further condition on `m*`, `r` or `Γ`.
--
--   Each factor is bounded by its own extreme and **all three extremes are attained simultaneously**, at
--   `(r, m*, Γ, B) = (1, 0, 8, 1)`: `r ≥ 1` gives `(r+1)/r ≤ 2`; `m* ≥ 0` caps the exponent at
--   `9/(32(m*+1)) ≤ 9/32`; and `1/(m*+1) ≤ 1` caps the root at `1 + B ≤ 2`. So the crude
--   separate-factor argument loses nothing here, and `cZero_eq_four_mul_exp_at_worst` shows the value is
--   reached — this is a maximum, not an estimate.
--
--   Weakening `2` to this costs a factor `2.6495` in `t₀` (see `tZero_anti`), hence `2.6495^{m*+1}` in
--   the error bound `(t/t₀)^{m*+1}` at fixed `t`, and it shrinks `log(t₀/t)` — the denominator of
--   `w* = k_o + 𝒪(log(1/ε)/log(t₀/t))` — by `ln 2.6495 = 0.974`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L645-L665
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L645-L665

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.cZero_le_four_mul_exp {r m G B : ℝ} (h : Admissible r m G) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    cZero r m G B ≤ 4 * exp (9 / 32) := by sorry
