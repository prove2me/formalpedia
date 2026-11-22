-- Prove2me | Theorems.Thm_Lean4LPD_sum_pow_le
-- name    : Lean4LPD.sum_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:31.388246+00:00
-- url     : https://prove2.me/theorems/89253834-9d72-4888-9d2d-1b16bc58118c
-- title:
--   Lean4 LPD: sum pow le
-- statement:
--   **`Σ_{d=1}^{r} d^m ≤ (r+1)^{m+1}/(m+1)`**, the integral comparison, by telescoping
--   `pow_le_sub_pow`. Written over `range r` with body `(i+1)^m` so that no `ℕ` subtraction appears.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/StepSum.lean#L97-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/StepSum.lean#L97-L117

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.sum_pow_le (m r : ℕ) :
    ∑ i ∈ range r, ((i : ℝ) + 1) ^ m ≤ ((r : ℝ) + 1) ^ (m + 1) / ((m : ℝ) + 1) := by sorry
