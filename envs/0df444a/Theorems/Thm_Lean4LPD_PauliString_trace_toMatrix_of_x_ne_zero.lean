-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trace_toMatrix_of_x_ne_zero
-- name    : Lean4LPD.PauliString.trace_toMatrix_of_x_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:54.410201+00:00
-- url     : https://prove2.me/theorems/2218c684-2b59-43eb-80e4-1a7d17071d2e
-- title:
--   Pauli String: trace to Matrix of x ne zero
-- statement:
--   A Pauli operator with a non-trivial `X`-part is traceless: it is a permutation matrix pattern
--   with no fixed points.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L152-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L152-L154

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

theorem Lean4LPD.PauliString.trace_toMatrix_of_x_ne_zero (hu : u.x ≠ 0) : (toMatrix u).trace = 0 := by sorry
