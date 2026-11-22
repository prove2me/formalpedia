-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_toMatrix_iff
-- name    : Lean4LPD.PauliString.isSelfAdjoint_toMatrix_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:09:11.773802+00:00
-- url     : https://prove2.me/theorems/73c7a95b-3c5a-40db-b4b3-5650e0d03534
-- title:
--   Pauli String: is Self Adjoint to Matrix iff
-- statement:
--   **Hermiticity transfers in both directions.** `toMatrix_star` alone gives only
--   symbol-to-operator; faithfulness supplies the converse, so a Pauli handed over as a self-adjoint
--   *operator* — which is how the generators `G_g` enter `apd:thm:local_flow_k_local` — is a
--   self-adjoint Pauli string, and `isSelfAdjoint_iff_mul_self_eq_one` applies to it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L409-L415
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L409-L415

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

theorem Lean4LPD.PauliString.isSelfAdjoint_toMatrix_iff {s : PauliString n} :
    IsSelfAdjoint (toMatrix s) ↔ IsSelfAdjoint s := by sorry
