-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_right
-- name    : Lean4LPD.PauliString.sympForm_mul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:06.993812+00:00
-- url     : https://prove2.me/theorems/9d9c9315-f235-4e0b-9e57-d9f5ebfc965c
-- title:
--   Pauli String: symp Form mul right
-- statement:
--   The symplectic form is **bilinear on the right**: `⟪u, s t⟫ = ⟪u, s⟫ + ⟪u, t⟫`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L275-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L275-L278

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

theorem Lean4LPD.PauliString.sympForm_mul_right (u s t : PauliString n) :
    sympForm u (s * t) = sympForm u s + sympForm u t := by sorry
