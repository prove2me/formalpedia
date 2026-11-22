-- Prove2me | Theorems.Thm_Lean4LPD_exp_factor_le_sharp
-- name    : Lean4LPD.exp_factor_le_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:38.973432+00:00
-- url     : https://prove2.me/theorems/32ee9522-51c6-4460-9e44-2a254a7368e5
-- title:
--   Lean4 LPD: exp factor le sharp
-- statement:
--   A sharper bound on the exponential factor than the `64/55` of `exp_factor_le`, under the same
--   hypotheses: `exp (9/64) ≤ 1439/1250`, via Mathlib's third-order `Real.exp_bound'` rather than
--   `exp y ≤ 1/(1−y)`.
--
--   **The sharpening is needed for `cZero_le_two_of_gamma_le_seven`.** With `Γ ≤ 7` the first factor
--   is bounded only by `39/32`, and `(39/32)·(64/55)·√2 ≈ 2.0056 > 2`: the two uniform bounds are
--   attained at different points, so their product overshoots. The cruder estimate
--   `exp y ≤ 1 + y + y²` is not enough either: it gives `≈ 2.00003`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L390-L402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L390-L402

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.exp_factor_le_sharp {r m G : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) :
    exp (9 / 4 * (m + 1) / (r * G)) ≤ 1439 / 1250 := by sorry
