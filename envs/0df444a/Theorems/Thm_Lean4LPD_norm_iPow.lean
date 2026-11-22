-- Prove2me | Theorems.Thm_Lean4LPD_norm_iPow
-- name    : Lean4LPD.norm_iPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:23.790919+00:00
-- url     : https://prove2.me/theorems/c7603d84-7510-4656-b1cf-694cdb2363a4
-- title:
--   Lean4 LPD: norm i Pow
-- statement:
--   Fourth roots of unity have modulus one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L101-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L101-L102

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.norm_iPow (k : ZMod 4) : ‖iPow k‖ = 1 := by sorry
