-- Prove2me | Theorems.Thm_Lean4LPD_cZero_le_two_of_gamma_le_seven
-- name    : Lean4LPD.cZero_le_two_of_gamma_le_seven
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:04:15.193046+00:00
-- url     : https://prove2.me/theorems/926ee91f-73ca-49a3-993b-4ffd95065c47
-- title:
--   Lean4 LPD: c Zero le two of gamma le seven
-- statement:
--   **`c₀ ≤ 2` at the integer cap `Γ ≤ 7`**, with `Admissible r m G`, `1 ≤ m` and `0 ≤ B ≤ 1`.
--   This is *not* a corollary of `cZero_le_two`: here `Admissible` yields only `r ≥ 32/7 ≈ 4.571`, so
--   `5 ≤ r` is unavailable.
--
--   The cap cannot be raised to 8: `two_lt_cZero_of_admissible_four` is `Admissible 4 1 8` with
--   `c₀ ≈ 2.0347`, so no separate witness is needed. Over the reals the threshold (at `m* = 1`,
--   `B = 1`) is `32(√2·e^{−9/64} − 1) ≈ 7.3181`; seven is the largest sufficient **integer** cap. The
--   extremal value is `c₀(32/7, 1, 7, 1) ≈ 1.9838`, a margin of 0.81% below 2, which is why
--   `exp_factor_le_sharp` is required.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L431-L450
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L431-L450

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.cZero_le_two_of_gamma_le_seven {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m)
    (hG7 : G ≤ 7) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 2 := by sorry
