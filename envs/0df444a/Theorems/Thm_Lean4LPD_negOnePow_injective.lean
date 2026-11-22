-- Prove2me | Theorems.Thm_Lean4LPD_negOnePow_injective
-- name    : Lean4LPD.negOnePow_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:23.405057+00:00
-- url     : https://prove2.me/theorems/a85066c8-e8f1-4a20-bd41-be3d33918297
-- title:
--   Lean4 LPD: neg One Pow injective
-- statement:
--   The Lean4 LPD construction uses the neg One Pow injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L149-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L149-L155

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

theorem Lean4LPD.negOnePow_injective : Function.Injective negOnePow := by sorry
