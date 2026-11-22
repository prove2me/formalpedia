-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_phaseMul
-- name    : Lean4LPD.PauliString.toMatrix_phaseMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:06:52.623796+00:00
-- url     : https://prove2.me/theorems/7a91b0c4-0500-4d69-ad6b-3a5e4bd2d855
-- title:
--   Pauli String: to Matrix phase Mul
-- statement:
--   The Pauli String construction uses the to Matrix phase Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L246-L253
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L246-L253

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

theorem Lean4LPD.PauliString.toMatrix_phaseMul (k : ZMod 4) (s : PauliString n) :
    toMatrix (phaseMul k s) = iPow k • toMatrix s := by sorry
