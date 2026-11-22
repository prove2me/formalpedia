-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_injective
-- name    : Lean4LPD.PauliString.toMatrix_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:20.31+00:00
-- url     : https://prove2.me/theorems/a3b32b85-2342-4a94-b786-babbb5ee3a5d
-- title:
--   Pauli String: to Matrix injective
-- statement:
--   **The representation is faithful.** Distinct Pauli strings — including strings differing only
--   in their phase — are distinct operators, so nothing proved through `toMatrix` is a statement about
--   a collapsed model.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L301-L327
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L301-L327

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

theorem Lean4LPD.PauliString.toMatrix_injective : Function.Injective (toMatrix (n := n)) := by sorry
