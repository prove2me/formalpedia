-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul_ne_smul
-- name    : Lean4LPD.PauliString.toMatrix_mul_ne_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:36.841666+00:00
-- url     : https://prove2.me/theorems/899fbfde-2f33-44d5-b2d3-d2c850c6a5c7
-- title:
--   Pauli String: to Matrix mul ne smul
-- statement:
--   The same statement, named for what it is used for.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L462-L463
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L462-L463

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

theorem Lean4LPD.PauliString.toMatrix_mul_ne_smul (h : sympForm G s = 1) (c : ℂ) :
    toMatrix (G * s) ≠ c • toMatrix s := by sorry
