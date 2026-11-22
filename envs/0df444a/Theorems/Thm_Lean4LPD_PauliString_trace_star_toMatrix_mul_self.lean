-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trace_star_toMatrix_mul_self
-- name    : Lean4LPD.PauliString.trace_star_toMatrix_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:00.12581+00:00
-- url     : https://prove2.me/theorems/39605320-dff7-4925-83a7-f8d780126032
-- title:
--   Pauli String: trace star to Matrix mul self
-- statement:
--   Every Pauli operator has squared Hilbert–Schmidt norm `2^n`. With the `2^{-n/2}` normalization
--   of `def:pauli_basis` this is the diagonal case `Tr(s s) = 1` of its orthonormality relation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L200-L205
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L200-L205

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

theorem Lean4LPD.PauliString.trace_star_toMatrix_mul_self (s : PauliString n) :
    (star (toMatrix s) * toMatrix s).trace = (2 : ℂ) ^ n := by sorry
