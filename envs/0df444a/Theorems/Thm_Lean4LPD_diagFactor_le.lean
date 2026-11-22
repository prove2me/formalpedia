-- Prove2me | Theorems.Thm_Lean4LPD_diagFactor_le
-- name    : Lean4LPD.diagFactor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:25.254804+00:00
-- url     : https://prove2.me/theorems/e9c196fd-0b13-4269-8035-7e3c3363bdd2
-- title:
--   Lean4 LPD: diag Factor le
-- statement:
--   **`(2j−1)^j/(j!)² ≤ (9/4)^{j-1}` for every `j ≥ 2`**, with equality at `j = 2`, where both
--   sides are `9/4`. By induction on `j` from the uniform ratio bound `diagFactor_ratio`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/PartFactor.lean#L216-L233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/PartFactor.lean#L216-L233

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.diagFactor_le (j : ℕ) (hj : 2 ≤ j) : diagFactor j ≤ (9 / 4 : ℝ) ^ (j - 1) := by sorry
