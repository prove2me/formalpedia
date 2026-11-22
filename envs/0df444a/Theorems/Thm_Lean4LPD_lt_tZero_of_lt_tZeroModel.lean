-- Prove2me | Theorems.Thm_Lean4LPD_lt_tZero_of_lt_tZeroModel
-- name    : Lean4LPD.lt_tZero_of_lt_tZeroModel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:05:18.366809+00:00
-- url     : https://prove2.me/theorems/88e7c80c-7ede-462f-a2e9-31147b384ae0
-- title:
--   Lean4 LPD: lt t Zero of lt t Zero Model
-- statement:
--   The consequence used downstream: the short-time regime of the model threshold sits inside
--   that of `apd:eq:time_condition`, i.e. `t < tZeroModel` implies `t < t₀`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Total.lean#L126-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Total.lean#L126-L129

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.lt_tZero_of_lt_tZeroModel {r m G B kh a t : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m)
    (hr5 : 5 ≤ r) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hkh : 1 < kh) (ha : 0 < a)
    (ht : t < tZeroModel G kh a) : t < tZero (cZero r m G B) G kh a := by sorry
