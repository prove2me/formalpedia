-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_norm_coeffVec
-- name    : Lean4LPD.PauliString.norm_coeffVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:23.530036+00:00
-- url     : https://prove2.me/theorems/d74a1b5e-2de8-4399-9360-56342fedaf62
-- title:
--   Pauli String: norm coeff Vec
-- statement:
--   **`‖O‖_{2,normalized} = ‖x‖_{ℓ²}`**, as an identity of norms: the Pauli 2-norm of the operator
--   *is* the
--   `ℓ²` norm of its coefficient vector.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L371-L373
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L371-L373

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
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.norm_coeffVec (O : Matrix (Bits n) (Bits n) ℂ) : ‖coeffVec O‖ = pauliNorm O := by sorry
