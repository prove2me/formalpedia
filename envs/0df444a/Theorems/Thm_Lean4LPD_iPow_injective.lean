-- Prove2me | Theorems.Thm_Lean4LPD_iPow_injective
-- name    : Lean4LPD.iPow_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:55.808811+00:00
-- url     : https://prove2.me/theorems/b60341a5-5a5a-4a59-8afe-cfb1e8fcaa5f
-- title:
--   Lean4 LPD: i Pow injective
-- statement:
--   The Lean4 LPD construction uses the i Pow injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L175-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L175-L179

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

theorem Lean4LPD.iPow_injective : Function.Injective iPow := by sorry
