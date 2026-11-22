-- Prove2me | Theorems.Thm_Lean4LPD_iPow_eq_one_iff
-- name    : Lean4LPD.iPow_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:47.866933+00:00
-- url     : https://prove2.me/theorems/835d5541-6158-4a59-b3fb-ea61e86e64da
-- title:
--   Lean4 LPD: i Pow eq one iff
-- statement:
--   The Lean4 LPD construction uses the i Pow eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L162-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L162-L173

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

theorem Lean4LPD.iPow_eq_one_iff {k : ZMod 4} : iPow k = 1 ↔ k = 0 := by sorry
