-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_zero_or_one
-- name    : Lean4LPD.PauliString.sympForm_eq_zero_or_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:07.105305+00:00
-- url     : https://prove2.me/theorems/82dfe1c1-289b-4776-8c70-6cf19beb70b5
-- title:
--   Pauli String: symp Form eq zero or one
-- statement:
--   **The dichotomy is exhaustive.** The symplectic form takes only the values `0` and `1`, so
--   there is no third case beyond the two that `apd:eq:pauli_rotation_branch` lists.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L370-L372
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L370-L372

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

theorem Lean4LPD.PauliString.sympForm_eq_zero_or_one (s t : PauliString n) :
    sympForm s t = 0 ∨ sympForm s t = 1 := by sorry
