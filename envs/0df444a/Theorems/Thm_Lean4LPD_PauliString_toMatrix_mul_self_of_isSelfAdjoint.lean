-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul_self_of_isSelfAdjoint
-- name    : Lean4LPD.PauliString.toMatrix_mul_self_of_isSelfAdjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:00.177748+00:00
-- url     : https://prove2.me/theorems/a93ab6ae-d11f-42f1-8930-53b31bed3f3b
-- title:
--   Pauli String: to Matrix mul self of is Self Adjoint
-- statement:
--   A Hermitian Pauli string is an **involution**: discharges `hG : G * G = 1`, the hypothesis the
--   two branch lemmas and `rot_mem_unitary` carry (`rot_zero`, `commute_rot`,
--   `rot_mul_eq_mul_rot_neg` and `star_rot` do not). Note this comes from the *same* hypothesis as
--   self-adjointness — `Pauli/Basic.lean`'s `isSelfAdjoint_iff_mul_self_eq_one`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L389-L391
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L389-L391

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

theorem Lean4LPD.PauliString.toMatrix_mul_self_of_isSelfAdjoint (h : IsSelfAdjoint s) :
    toMatrix s * toMatrix s = 1 := by sorry
