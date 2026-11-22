-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul_toMatrix_inv
-- name    : Lean4LPD.PauliString.toMatrix_mul_toMatrix_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:08:00.671046+00:00
-- url     : https://prove2.me/theorems/99857da2-5810-48dc-a175-5b539a431f4a
-- title:
--   Pauli String: to Matrix mul to Matrix inv
-- statement:
--   Every Pauli operator is invertible, with `toMatrix s⁻¹` as inverse.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L394-L396
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L394-L396

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

theorem Lean4LPD.PauliString.toMatrix_mul_toMatrix_inv (s : PauliString n) :
    toMatrix s * toMatrix s⁻¹ = 1 := by sorry
