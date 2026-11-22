-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_apply_ne
-- name    : Lean4LPD.PauliString.toMatrix_apply_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:30.477062+00:00
-- url     : https://prove2.me/theorems/1c3669bd-e398-4f96-b767-6b37f52d64d4
-- title:
--   Pauli String: to Matrix apply ne
-- statement:
--   The Pauli String construction uses the to Matrix apply ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L238-L239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L238-L239

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

theorem Lean4LPD.PauliString.toMatrix_apply_ne (s : PauliString n) {a b : Bits n} (h : a ≠ b + s.x) :
    toMatrix s a b = 0 := by sorry
