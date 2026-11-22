-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNormSq_eq_trace
-- name    : Lean4LPD.PauliString.pauliNormSq_eq_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:13.806374+00:00
-- url     : https://prove2.me/theorems/34722260-6e76-41a9-b324-c5a21c6b7058
-- title:
--   Pauli String: pauli Norm Sq eq trace
-- statement:
--   `‖O‖_{2,normalized}² = 2^{-n} Tr(O† O)`: the entrywise definition `pauliNormSq` agrees with
--   the trace
--   form of the normalized Schatten 2-norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L203-L215
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L203-L215

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

theorem Lean4LPD.PauliString.pauliNormSq_eq_trace (O : Matrix (Bits n) (Bits n) ℂ) :
    ((pauliNormSq O : ℝ) : ℂ) = ((2 : ℂ) ^ n)⁻¹ * (star O * O).trace := by sorry
