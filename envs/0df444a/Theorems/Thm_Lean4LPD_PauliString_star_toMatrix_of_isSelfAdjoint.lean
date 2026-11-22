-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_star_toMatrix_of_isSelfAdjoint
-- name    : Lean4LPD.PauliString.star_toMatrix_of_isSelfAdjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:06.806805+00:00
-- url     : https://prove2.me/theorems/74bb63d7-0254-4c59-9cf4-e185b08a776e
-- title:
--   Pauli String: star to Matrix of is Self Adjoint
-- statement:
--   A Hermitian Pauli string is a **self-adjoint operator**: discharges `star G = G` in
--   `Lean4LPD.rot_mem_unitary`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L382-L383
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L382-L383

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

theorem Lean4LPD.PauliString.star_toMatrix_of_isSelfAdjoint (h : IsSelfAdjoint s) :
    star (toMatrix s) = toMatrix s := by sorry
