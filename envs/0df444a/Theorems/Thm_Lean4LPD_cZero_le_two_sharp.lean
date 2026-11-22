-- Prove2me | Theorems.Thm_Lean4LPD_cZero_le_two_sharp
-- name    : Lean4LPD.cZero_le_two_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:38.326982+00:00
-- url     : https://prove2.me/theorems/f90eb86c-87c8-4452-8123-0bd964a83b91
-- title:
--   Lean4 LPD: c Zero le two sharp
-- statement:
--   **`c₀ ≤ (384/275)·√2 ≈ 1.9748`** whenever `Admissible r m G`, `1 ≤ m`, `5 ≤ r` and
--   `0 ≤ B ≤ 1`. The three factors are bounded separately: `(r+1)/r ≤ 6/5` from `r ≥ 5`, the
--   exponential by `64/55` from `rΓ ≥ 8(m*+1)²` (`exp_factor_le`), and the root by `√2` from `m* ≥ 1`
--   with `B ≤ 1` (`root_factor_le`).
--
--   `B ≤ 1` is the range delivered by the step-count condition `r ≥ 8e²w₂αt` (see the module
--   docstring); a smaller range such as `B ≤ 1/2` is covered a fortiori.
--
--   `hm1` and `hr5` are explicit arguments rather than fields of `Admissible`, and neither can be
--   dropped: `two_lt_cZero_of_m_zero` and `two_lt_cZero_of_admissible_four` give admissible points with
--   `c₀ > 2` at which only `1 ≤ m`, respectively only `5 ≤ r`, is violated.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L176-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L176-L194

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.cZero_le_two_sharp {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) (hr5 : 5 ≤ r)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 384 / 275 * Real.sqrt 2 := by sorry
