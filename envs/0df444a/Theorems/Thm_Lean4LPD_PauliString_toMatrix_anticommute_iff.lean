-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_anticommute_iff
-- name    : Lean4LPD.PauliString.toMatrix_anticommute_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:09:10.472305+00:00
-- url     : https://prove2.me/theorems/2dfcd4f0-8521-4ba2-b243-19e9e9c355d2
-- title:
--   Pauli String: to Matrix anticommute iff
-- statement:
--   The anticommuting branch condition, likewise an **iff**.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L370-L376
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L370-L376

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n}

theorem Lean4LPD.PauliString.toMatrix_anticommute_iff (s t : PauliString n) :
    toMatrix s * toMatrix t = -(toMatrix t * toMatrix s) ↔ sympForm s t = 1 := by sorry
