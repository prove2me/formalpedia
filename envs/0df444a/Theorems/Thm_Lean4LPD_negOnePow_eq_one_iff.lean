-- Prove2me | Theorems.Thm_Lean4LPD_negOnePow_eq_one_iff
-- name    : Lean4LPD.negOnePow_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:43.596957+00:00
-- url     : https://prove2.me/theorems/d79b6888-fb40-4ebb-81e5-da5931cf20e3
-- title:
--   Lean4 LPD: neg One Pow eq one iff
-- statement:
--   The Lean4 LPD construction uses the neg One Pow eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L157-L160
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L157-L160

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

theorem Lean4LPD.negOnePow_eq_one_iff {a : ZMod 2} : negOnePow a = 1 ↔ a = 0 := by sorry
