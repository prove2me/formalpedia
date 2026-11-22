-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_anticommute
-- name    : Lean4LPD.PauliString.toMatrix_anticommute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:18.620133+00:00
-- url     : https://prove2.me/theorems/4bf382f2-b512-4344-961f-ca5b2b572def
-- title:
--   Pauli String: to Matrix anticommute
-- statement:
--   Anticommuting Pauli strings give anticommuting operators — the hypothesis
--   `Lean4LPD.rot_conj_of_anticommute` takes, spelled the way that file spells it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L354-L357
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L354-L357

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

theorem Lean4LPD.PauliString.toMatrix_anticommute (h : sympForm s t = 1) :
    toMatrix s * toMatrix t = -(toMatrix t * toMatrix s) := by sorry
