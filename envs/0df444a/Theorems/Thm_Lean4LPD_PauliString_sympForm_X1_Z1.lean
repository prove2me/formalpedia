-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_X1_Z1
-- name    : Lean4LPD.PauliString.sympForm_X1_Z1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:08:33.390418+00:00
-- url     : https://prove2.me/theorems/082dd8bb-edb4-4c3d-93cc-407c9f50e43f
-- title:
--   Pauli String: symp Form X1 Z1
-- statement:
--   **`X` and `Z` anticommute**, so the anticommuting branch has a witness and every theorem
--   conditioned on `sympForm G s = 1` says something.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L478-L478
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L478-L478

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

theorem Lean4LPD.PauliString.sympForm_X1_Z1 : sympForm X1 Z1 = 1 := by sorry
