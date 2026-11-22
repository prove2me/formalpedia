-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_left
-- name    : Lean4LPD.PauliString.sympForm_mul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:08:17.097995+00:00
-- url     : https://prove2.me/theorems/8a036bee-eb41-4821-9561-72e9eb827f04
-- title:
--   Pauli String: symp Form mul left
-- statement:
--   The symplectic form is **bilinear on the left**.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L281-L284
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L281-L284

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

theorem Lean4LPD.PauliString.sympForm_mul_left (s t u : PauliString n) :
    sympForm (s * t) u = sympForm s u + sympForm t u := by sorry
