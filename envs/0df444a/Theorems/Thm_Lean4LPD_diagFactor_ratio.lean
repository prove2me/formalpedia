-- Prove2me | Theorems.Thm_Lean4LPD_diagFactor_ratio
-- name    : Lean4LPD.diagFactor_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:22.408143+00:00
-- url     : https://prove2.me/theorems/d8317774-3657-4c9f-9c51-a6bcb64e1c97
-- title:
--   Lean4 LPD: diag Factor ratio
-- statement:
--   The uniform ratio bound: `f(j+1) ≤ (9/4) f(j)` for every `j ≥ 2`, where `f = diagFactor`.
--   `((2j+1)/(2j−1))^j ≤ exp(2j/(2j−1)) ≤ exp(4/3) ≤ 4.03`, and `(2j+1)·4.03 ≤ (9/4)(j+1)²` for
--   `j ≥ 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/PartFactor.lean#L159-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/PartFactor.lean#L159-L212

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.diagFactor_ratio {j : ℕ} (hj : 2 ≤ j) : diagFactor (j + 1) ≤ 9 / 4 * diagFactor j := by sorry
