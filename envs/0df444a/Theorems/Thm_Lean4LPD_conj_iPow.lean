-- Prove2me | Theorems.Thm_Lean4LPD_conj_iPow
-- name    : Lean4LPD.conj_iPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:58.40485+00:00
-- url     : https://prove2.me/theorems/f25cc5fd-0332-4005-890d-26d71997b9ed
-- title:
--   Lean4 LPD: conj i Pow
-- statement:
--   The Lean4 LPD construction uses the conj i Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L184-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L184-L192

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

theorem Lean4LPD.conj_iPow (k : ZMod 4) : starRingEnd ℂ (iPow k) = iPow (-k) := by sorry
