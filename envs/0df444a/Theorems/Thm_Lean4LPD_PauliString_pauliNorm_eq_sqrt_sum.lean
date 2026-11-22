-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_eq_sqrt_sum
-- name    : Lean4LPD.PauliString.pauliNorm_eq_sqrt_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:01.880813+00:00
-- url     : https://prove2.me/theorems/0c4f5696-2d01-471f-a9b5-ef9abf3bcaa8
-- title:
--   Pauli String: pauli Norm eq sqrt sum
-- statement:
--   **`‖O‖_{2,normalized} = ‖x‖_{ℓ²}`**, as norms rather than squares.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L324-L326
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L324-L326

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

theorem Lean4LPD.PauliString.pauliNorm_eq_sqrt_sum (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm O = Real.sqrt (∑ p : PauliIndex n, ‖coeff O p‖ ^ 2) := by sorry
