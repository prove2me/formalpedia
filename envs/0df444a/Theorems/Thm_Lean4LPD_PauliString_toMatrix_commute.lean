-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_commute
-- name    : Lean4LPD.PauliString.toMatrix_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:33.579551+00:00
-- url     : https://prove2.me/theorems/bad3d180-e116-443b-8e58-ac9e04a57634
-- title:
--   Pauli String: to Matrix commute
-- statement:
--   Commuting Pauli strings give commuting operators.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L347-L350
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L347-L350

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

theorem Lean4LPD.PauliString.toMatrix_commute (h : sympForm s t = 0) :
    Commute (toMatrix s) (toMatrix t) := by sorry
