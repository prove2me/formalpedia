-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_self
-- name    : Lean4LPD.PauliString.sympForm_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:57:58.726384+00:00
-- url     : https://prove2.me/theorems/5b6a1cef-f9bf-461c-84d8-896e1df7e0cf
-- title:
--   Pauli String: symp Form self
-- statement:
--   The form is alternating: every Pauli string commutes with itself.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L287-L290
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L287-L290

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

theorem Lean4LPD.PauliString.sympForm_self (s : PauliString n) : sympForm s s = 0 := by sorry
