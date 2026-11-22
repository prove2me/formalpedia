-- Prove2me | Theorems.Thm_Lean4LPD_pow_le_sub_pow
-- name    : Lean4LPD.pow_le_sub_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:25.714451+00:00
-- url     : https://prove2.me/theorems/627a6a8c-25f1-4ce3-b1de-cb48c23ff362
-- title:
--   Lean4 LPD: pow le sub pow
-- statement:
--   `d^m ≤ ((d+1)^{m+1} − d^{m+1})/(m+1)` for `d ≥ 1`, the integral comparison behind the slot
--   count, in the form Bernoulli's inequality supplies it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/StepSum.lean#L71-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/StepSum.lean#L71-L93

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.pow_le_sub_pow {d : ℝ} (hd : 1 ≤ d) (m : ℕ) :
    ((m : ℝ) + 1) * d ^ m ≤ (d + 1) ^ (m + 1) - d ^ (m + 1) := by sorry
