-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_commute_or_anticommute
-- name    : Lean4LPD.PauliString.toMatrix_commute_or_anticommute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:08:50.721258+00:00
-- url     : https://prove2.me/theorems/dff39f4b-5078-4dec-a9f7-8a34e9f1138e
-- title:
--   Pauli String: to Matrix commute or anticommute
-- statement:
--   **Any two Pauli operators either commute or anticommute.** The operator form of
--   `PauliString.commute_or_anticommute`, and the exhaustiveness that
--   `Lean4LPD.rot_conj_of_commute` / `Lean4LPD.rot_conj_of_anticommute` presuppose: those two cover a
--   commuting and an anticommuting generator, and over an abstract algebra nothing rules out a third
--   case. For Pauli operators it shows that the two cases of `apd:eq:pauli_rotation_branch` are the
--   only ones.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L337-L344
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L337-L344

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

theorem Lean4LPD.PauliString.toMatrix_commute_or_anticommute (s t : PauliString n) :
    Commute (toMatrix s) (toMatrix t) ∨
      toMatrix s * toMatrix t = -(toMatrix t * toMatrix s) := by sorry
