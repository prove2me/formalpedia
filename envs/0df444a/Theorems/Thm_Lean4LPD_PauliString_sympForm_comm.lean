-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_comm
-- name    : Lean4LPD.PauliString.sympForm_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:08:14.313837+00:00
-- url     : https://prove2.me/theorems/31b5c7b0-3601-435d-9bd6-e02ba8f9a5e4
-- title:
--   Pauli String: symp Form comm
-- statement:
--   The Pauli String construction uses the symp Form comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L270-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L270-L272

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

theorem Lean4LPD.PauliString.sympForm_comm (s t : PauliString n) : sympForm s t = sympForm t s := by sorry
