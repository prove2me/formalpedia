-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_apply_add
-- name    : Lean4LPD.PauliString.toMatrix_apply_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:05.174597+00:00
-- url     : https://prove2.me/theorems/d9d0e07d-0598-42cc-b695-07d88cc44727
-- title:
--   Pauli String: to Matrix apply add
-- statement:
--   The one non-zero entry of each column.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L234-L236
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L234-L236

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

theorem Lean4LPD.PauliString.toMatrix_apply_add (s : PauliString n) (b : Bits n) :
    toMatrix s (b + s.x) b = iPow s.phase * negOnePow (s.z ⬝ᵥ b) := by sorry
