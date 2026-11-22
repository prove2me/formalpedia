-- Prove2me | Theorems.Thm_Lean4LPD_cZero_le_two_of_gamma_le_six
-- name    : Lean4LPD.cZero_le_two_of_gamma_le_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:04:10.393577+00:00
-- url     : https://prove2.me/theorems/290b1d27-62b9-4325-ba85-a36db012d64d
-- title:
--   Lean4 LPD: c Zero le two of gamma le six
-- statement:
--   **`c₀ ≤ 2` under a cap of 6 on the effective layer count**, with `Admissible r m G`, `1 ≤ m`
--   and `0 ≤ B ≤ 1`. Immediate from `cZero_le_two` and `le_r_of_gamma_le_six`, so it inherits the
--   constant `(384/275)√2 ≈ 1.9748` rather than the narrow margin `1.9838` of
--   `cZero_le_two_of_gamma_le_seven`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L418-L420
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L418-L420

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.cZero_le_two_of_gamma_le_six {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m)
    (hG6 : G ≤ 6) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 2 := by sorry
