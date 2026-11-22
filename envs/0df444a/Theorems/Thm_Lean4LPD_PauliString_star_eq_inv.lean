-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_star_eq_inv
-- name    : Lean4LPD.PauliString.star_eq_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:43.587819+00:00
-- url     : https://prove2.me/theorems/8616a85b-393b-4cdd-b80c-48b28f5ab9f5
-- title:
--   Pauli String: star eq inv
-- statement:
--   Pauli strings are **unitary**: the adjoint is the inverse. Definitional here, given how `star`
--   is defined; the theorem with content is `toMatrix_star`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L251-L251
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L251-L251

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}

theorem Lean4LPD.PauliString.star_eq_inv (s : PauliString n) : star s = s⁻¹ := by sorry
