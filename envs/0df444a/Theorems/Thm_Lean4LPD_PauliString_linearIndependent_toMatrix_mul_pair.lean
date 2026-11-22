-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_linearIndependent_toMatrix_mul_pair
-- name    : Lean4LPD.PauliString.linearIndependent_toMatrix_mul_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:09:14.936883+00:00
-- url     : https://prove2.me/theorems/818a2692-d700-48f2-a7e4-a6eb042676c9
-- title:
--   Pauli String: linear Independent to Matrix mul pair
-- statement:
--   **The two branch terms are linearly independent.** Non-collinearity (`toMatrix_mul_ne_smul`) is
--   not by itself linear independence — it leaves open `a • A = 0` with `a ≠ 0` — and what closes the
--   gap is `toMatrix_ne_zero`. This is the property `Rotation.lean` names as what the damping
--   consequence of `apd:eq:pauli_rotation_branch` needs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L469-L483
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L469-L483

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

theorem Lean4LPD.PauliString.linearIndependent_toMatrix_mul_pair (h : sympForm G s = 1) :
    LinearIndependent ℂ ![toMatrix s, toMatrix (G * s)] := by sorry
