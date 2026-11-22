-- Prove2me | Theorems.Thm_Lean4LPD_pow_decayBase_antitone
-- name    : Lean4LPD.pow_decayBase_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:05:25.886262+00:00
-- url     : https://prove2.me/theorems/8b965c00-5a6e-45c1-9d10-4a0eac67660a
-- title:
--   Lean4 LPD: pow decay Base antitone
-- statement:
--   Under the short-time condition `apd:eq:time_condition` the bound decays in `m*`. Stated as
--   monotonicity of `q^{m+1}`: `q^{m+2} ≤ q^{m+1}` for `0 ≤ t < tZeroModel`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Total.lean#L151-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Total.lean#L151-L155

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.pow_decayBase_antitone {G kh a t : ℝ} (hG : 0 < G) (hkh : 1 < kh) (ha : 0 < a) (ht0 : 0 ≤ t)
    (ht : t < tZeroModel G kh a) (m : ℕ) :
    decayBase G kh a t ^ (m + 2) ≤ decayBase G kh a t ^ (m + 1) := by sorry
