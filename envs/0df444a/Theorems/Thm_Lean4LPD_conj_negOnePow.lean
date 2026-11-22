-- Prove2me | Theorems.Thm_Lean4LPD_conj_negOnePow
-- name    : Lean4LPD.conj_negOnePow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:06:52.78287+00:00
-- url     : https://prove2.me/theorems/31887500-e4e8-4b36-8def-7eca85d45ea9
-- title:
--   Lean4 LPD: conj neg One Pow
-- statement:
--   The Lean4 LPD construction uses the conj neg One Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L181-L182
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L181-L182

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

theorem Lean4LPD.conj_negOnePow (a : ZMod 2) : starRingEnd ℂ (negOnePow a) = negOnePow a := by sorry
