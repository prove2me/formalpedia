-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trace_star_toMatrix_mul_eq_zero
-- name    : Lean4LPD.PauliString.trace_star_toMatrix_mul_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:57.756419+00:00
-- url     : https://prove2.me/theorems/c506a763-ed9a-474b-a4aa-df3d7f889780
-- title:
--   Pauli String: trace star to Matrix mul eq zero
-- statement:
--   Two Pauli strings differing in their `X`- or `Z`-part are **orthogonal** operators.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L194-L196
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L194-L196

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

theorem Lean4LPD.PauliString.trace_star_toMatrix_mul_eq_zero (h : ¬(s.x = t.x ∧ s.z = t.z)) :
    (star (toMatrix s) * toMatrix t).trace = 0 := by sorry
