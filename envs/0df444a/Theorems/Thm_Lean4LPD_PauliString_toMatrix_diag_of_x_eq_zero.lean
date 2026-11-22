-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_diag_of_x_eq_zero
-- name    : Lean4LPD.PauliString.toMatrix_diag_of_x_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:54.664876+00:00
-- url     : https://prove2.me/theorems/5d95207a-9bb6-401c-aa85-75cd7d5d439a
-- title:
--   Pauli String: to Matrix diag of x eq zero
-- statement:
--   The Pauli String construction uses the to Matrix diag of x eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L144-L146
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L144-L146

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

theorem Lean4LPD.PauliString.toMatrix_diag_of_x_eq_zero (hu : u.x = 0) (a : Bits n) :
    toMatrix u a a = iPow u.phase * negOnePow (u.z ⬝ᵥ a) := by sorry
