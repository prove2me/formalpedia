-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul_ne_smul_aux
-- name    : Lean4LPD.PauliString.toMatrix_mul_ne_smul_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:55.058853+00:00
-- url     : https://prove2.me/theorems/14cf6395-f952-4928-a789-054975d45212
-- title:
--   Pauli String: to Matrix mul ne smul aux
-- statement:
--   **The two branch terms are independent.** When `G` anticommutes with `s`, the partner `G s` is
--   not a scalar multiple of `s`, so the `i sin(dt)` coefficient in `apd:eq:pauli_rotation_branch`
--   really is the amplitude of a *new* transition rather than a rescaling of the old one.
--
--   `Rotation.lean` states that the damping consequence of the branching rule needs exactly this and
--   that mere distinctness is not enough, exhibiting `G = Z`, `P = E₁₀` in
--   `Matrix (Fin 2) (Fin 2) ℂ` — both rotation hypotheses hold there and `G * P = -P`. That example
--   is not a Pauli string, and this theorem is why no Pauli string can play its role.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L449-L459
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L449-L459

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

theorem Lean4LPD.PauliString.toMatrix_mul_ne_smul_aux (h : sympForm G s = 1) (c : ℂ) :
    toMatrix (G * s) ≠ c • toMatrix s := by sorry
