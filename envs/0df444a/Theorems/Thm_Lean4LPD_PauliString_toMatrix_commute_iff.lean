-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_commute_iff
-- name    : Lean4LPD.PauliString.toMatrix_commute_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:08:55.15681+00:00
-- url     : https://prove2.me/theorems/7b92933f-ad4e-4616-a1e6-3e4ea921ddcd
-- title:
--   Pauli String: to Matrix commute iff
-- statement:
--   The commuting branch condition is an **iff** at the level of operators, not just an
--   implication: `toMatrix` is injective, so operators commuting forces the symbols to. Without this
--   the `if` in `pauli_rotation_branch` would be a sufficient condition for the paper's `[G,P] = 0`
--   rather than a rendering of it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L363-L367
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L363-L367

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

theorem Lean4LPD.PauliString.toMatrix_commute_iff (s t : PauliString n) :
    Commute (toMatrix s) (toMatrix t) ↔ sympForm s t = 0 := by sorry
