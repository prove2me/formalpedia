-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_diag_ne_zero_iff
-- name    : Lean4LPD.PauliString.diag_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:51.316116+00:00
-- url     : https://prove2.me/theorems/120199e0-feba-42e3-b532-353ca5b08093
-- title:
--   Pauli String: diag ne zero iff
-- statement:
--   In characteristic two a shift fixes a basis label only when it is trivial, so `toMatrix u` has
--   a non-empty diagonal exactly when its `X`-part vanishes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L131-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L131-L137

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

theorem Lean4LPD.PauliString.diag_ne_zero_iff (u : PauliString n) (a : Bits n) :
    a = a + u.x ↔ u.x = 0 := by sorry
