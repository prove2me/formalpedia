-- Prove2me | Theorems.Thm_Lean4LPD_decayBase_lt_one
-- name    : Lean4LPD.decayBase_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:59.799112+00:00
-- url     : https://prove2.me/theorems/85b6ad9b-b97e-4a1c-b7ba-7ea4538b390e
-- title:
--   Lean4 LPD: decay Base lt one
-- statement:
--   `q < 1` in the short-time regime `t < t₀` of `apd:eq:time_condition`, here with
--   `t₀ = tZeroModel`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Total.lean#L142-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Total.lean#L142-L147

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.decayBase_lt_one {G kh a t : ℝ} (hG : 0 < G) (hkh : 1 < kh) (ha : 0 < a)
    (ht : t < tZeroModel G kh a) : decayBase G kh a t < 1 := by sorry
