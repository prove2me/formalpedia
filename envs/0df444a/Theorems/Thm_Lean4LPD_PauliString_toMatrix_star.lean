-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_star
-- name    : Lean4LPD.PauliString.toMatrix_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:17.802811+00:00
-- url     : https://prove2.me/theorems/aca9f3f9-7cac-4a63-8819-b5808f4ec4da
-- title:
--   Pauli String: to Matrix star
-- statement:
--   **The representation respects the adjoint.** This is the theorem that justifies calling
--   `PauliString`'s `star` an adjoint at all — in `Pauli/Basic.lean` it is only *defined*, as the
--   group inverse.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L277-L289
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L277-L289

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

theorem Lean4LPD.PauliString.toMatrix_star (s : PauliString n) : star (toMatrix s) = toMatrix (star s) := by sorry
