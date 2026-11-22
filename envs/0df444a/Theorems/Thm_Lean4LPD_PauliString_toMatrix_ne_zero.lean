-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_ne_zero
-- name    : Lean4LPD.PauliString.toMatrix_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:17.660299+00:00
-- url     : https://prove2.me/theorems/1ed3f1c7-b628-43d4-b7fd-1a5fb7eafd08
-- title:
--   Pauli String: to Matrix ne zero
-- statement:
--   No Pauli operator is zero: the entry at `(b + x, b)` is `i^{phase}`, a fourth root of unity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L399-L403
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L399-L403

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

theorem Lean4LPD.PauliString.toMatrix_ne_zero (s : PauliString n) : toMatrix s ≠ 0 := by sorry
