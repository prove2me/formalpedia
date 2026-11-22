-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trace_toMatrix_of_x_eq_zero
-- name    : Lean4LPD.PauliString.trace_toMatrix_of_x_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:57.022477+00:00
-- url     : https://prove2.me/theorems/fc3b71b2-c54d-4396-8a12-421559f30b55
-- title:
--   Pauli String: trace to Matrix of x eq zero
-- statement:
--   With a trivial `X`-part the trace is the phase times a character sum over the `Z`-part.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L157-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L157-L161

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}

theorem Lean4LPD.PauliString.trace_toMatrix_of_x_eq_zero (hu : u.x = 0) :
    (toMatrix u).trace = iPow u.phase * ∑ b : Bits n, negOnePow (u.z ⬝ᵥ b) := by sorry
