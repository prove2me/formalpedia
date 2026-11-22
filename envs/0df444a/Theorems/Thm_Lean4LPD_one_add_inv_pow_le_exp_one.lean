-- Prove2me | Theorems.Thm_Lean4LPD_one_add_inv_pow_le_exp_one
-- name    : Lean4LPD.one_add_inv_pow_le_exp_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:24.446472+00:00
-- url     : https://prove2.me/theorems/b0fe3eca-9a38-4eee-8662-c9cb179f52f0
-- title:
--   Lean4 LPD: one add inv pow le exp one
-- statement:
--   `(1 + 1/j)^j ≤ e` for `j ≥ 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Entry.lean#L102-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Entry.lean#L102-L114

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.one_add_inv_pow_le_exp_one {j : ℕ} (hj : 1 ≤ j) :
    (1 + 1 / (j : ℝ)) ^ j ≤ Real.exp 1 := by sorry
