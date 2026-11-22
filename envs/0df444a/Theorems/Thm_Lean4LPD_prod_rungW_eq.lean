-- Prove2me | Theorems.Thm_Lean4LPD_prod_rungW_eq
-- name    : Lean4LPD.prod_rungW_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:26.968165+00:00
-- url     : https://prove2.me/theorems/7b0a0add-d419-4842-878a-02b6cdf572ab
-- title:
--   Lean4 LPD: prod rung W eq
-- statement:
--   **The rung product in closed form.** `∏_{j=2}^{n+1} w_j = (k_h−1)^n ∏_{i=1}^{n} (i+c)`,
--   written over `range n`. The second factor is smaller than the shifted product
--   `∏_{j=2}^{n+1}(j+c)` in which the estimate of `apd:eq:total_high_weight_norm` is displayed — see
--   `prod_shift_le` and `prod_shift_ratio`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/StepSum.lean#L167-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/StepSum.lean#L167-L176

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.prod_rungW_eq (kh1 c : ℝ) (n : ℕ) :
    ∏ i ∈ range n, rungW kh1 c (i + 2) = kh1 ^ n * ∏ i ∈ range n, ((i : ℝ) + 1 + c) := by sorry
