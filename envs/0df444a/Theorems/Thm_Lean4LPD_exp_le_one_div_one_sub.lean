-- Prove2me | Theorems.Thm_Lean4LPD_exp_le_one_div_one_sub
-- name    : Lean4LPD.exp_le_one_div_one_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:02.401566+00:00
-- url     : https://prove2.me/theorems/74283458-771c-4faa-a7ae-be7006ef7833
-- title:
--   Lean4 LPD: exp le one div one sub
-- statement:
--   `exp y ≤ 1/(1-y)` for `y < 1`, the upper bound on `Real.exp` used below. It is the
--   one-line consequence of `1 - y ≤ exp (-y)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L121-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L121-L131

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.exp_le_one_div_one_sub {y : ℝ} (hy : y < 1) : exp y ≤ 1 / (1 - y) := by sorry
