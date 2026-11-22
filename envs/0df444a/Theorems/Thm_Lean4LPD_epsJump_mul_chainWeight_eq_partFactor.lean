-- Prove2me | Theorems.Thm_Lean4LPD_epsJump_mul_chainWeight_eq_partFactor
-- name    : Lean4LPD.epsJump_mul_chainWeight_eq_partFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:48.719395+00:00
-- url     : https://prove2.me/theorems/9ed19637-67ba-4a7c-88fd-095f5b301dda
-- title:
--   Lean4 LPD: eps Jump mul chain Weight eq part Factor
-- statement:
--   **The jump/all-ones identity, including `a = 0`.**
--   This supplies the algebra behind `apd:eq:part_factor`, without dividing
--   by a possibly-zero angle factor or all-ones weight. The endpoint `j=m` is allowed and
--   is exactly the reservoir-entry comparison.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L119-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L119-L132

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.epsJump_mul_chainWeight_eq_partFactor {c : ℝ} (hc : 0 ≤ c) (kh1 a : ℝ)
    {j m : ℕ} (hjm : j ≤ m) :
    epsJump kh1 c a j m * chainWeight kh1 c a (m - j)
      = partFactor j ((m : ℝ) + c) * chainWeight kh1 c a m := by sorry
