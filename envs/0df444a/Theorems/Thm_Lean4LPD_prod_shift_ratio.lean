-- Prove2me | Theorems.Thm_Lean4LPD_prod_shift_ratio
-- name    : Lean4LPD.prod_shift_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:04:46.686106+00:00
-- url     : https://prove2.me/theorems/0bc125b3-e8a8-474e-9653-48a0bb2a893c
-- title:
--   Lean4 LPD: prod shift ratio
-- statement:
--   The shifted product exceeds the exact one by exactly the factor `(n+1+c)/(1+c)`:
--   `(∏_{i<n}(i+2+c)) · (1+c) = (∏_{i<n}(i+1+c)) · (n+1+c)`. Both products telescope against each
--   other, so the gap between them is a single ratio rather than a factor accumulating with `n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/StepSum.lean#L191-L204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/StepSum.lean#L191-L204

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.prod_shift_ratio (c : ℝ) (n : ℕ) :
    (∏ i ∈ range n, ((i : ℝ) + 2 + c)) * (1 + c)
      = (∏ i ∈ range n, ((i : ℝ) + 1 + c)) * ((n : ℝ) + 1 + c) := by sorry
