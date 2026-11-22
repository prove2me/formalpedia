-- Prove2me | Theorems.Thm_Lean4LPD_iPow_signPhase
-- name    : Lean4LPD.iPow_signPhase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:06:46.782429+00:00
-- url     : https://prove2.me/theorems/7e2ebdb7-3ba7-4cae-99c1-e963a4f1d9c3
-- title:
--   Lean4 LPD: i Pow sign Phase
-- statement:
--   The two characters agree where they must: `(-1)^a = i^{2a}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L136-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L136-L137

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

theorem Lean4LPD.iPow_signPhase (a : ZMod 2) : iPow (signPhase a) = negOnePow a := by sorry
