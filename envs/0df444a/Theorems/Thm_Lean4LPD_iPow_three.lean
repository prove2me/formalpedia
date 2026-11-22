-- Prove2me | Theorems.Thm_Lean4LPD_iPow_three
-- name    : Lean4LPD.iPow_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:11.622613+00:00
-- url     : https://prove2.me/theorems/314165be-5b87-46cb-af27-7b9e7b906f1b
-- title:
--   Lean4 LPD: i Pow three
-- statement:
--   The Lean4 LPD construction uses the i Pow three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L114-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L114-L117

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

theorem Lean4LPD.iPow_three : iPow 3 = -Complex.I := by sorry
