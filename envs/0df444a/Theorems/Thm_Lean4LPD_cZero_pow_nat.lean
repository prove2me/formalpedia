-- Prove2me | Theorems.Thm_Lean4LPD_cZero_pow_nat
-- name    : Lean4LPD.cZero_pow_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:10.948826+00:00
-- url     : https://prove2.me/theorems/58cbcf37-3621-4d03-8188-bd150e7eec15
-- title:
--   Lean4 LPD: c Zero pow nat
-- statement:
--   Raising `c₀` to the power `m + 1` recovers the correction factors of `apd:eq:c0` exactly:
--   `c₀^{m+1} = ((r+1)/r)^{m+1} · exp(9(m+1)²/(4rΓ)) · (1+B)`. This is an identity, valid for every
--   natural `m` including `m = 0`; it does not use the bound `c₀ ≤ 2` of `cZero_le_two`, which
--   requires `m ≥ 1` (see `two_lt_cZero_of_m_zero`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L283-L296
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L283-L296

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.cZero_pow_nat {r G B : ℝ} (hB : 0 ≤ B) (m : ℕ) :
    cZero r (m : ℝ) G B ^ (m + 1) =
      ((r + 1) / r) ^ (m + 1) *
        Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / (r * G)) * (1 + B) := by sorry
