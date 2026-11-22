-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_X1
-- name    : Lean4LPD.PauliString.isSelfAdjoint_X1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:11.678422+00:00
-- url     : https://prove2.me/theorems/06f31173-2aca-4e1a-a349-7c8f7ef3f233
-- title:
--   Pauli String: is Self Adjoint X1
-- statement:
--   The Pauli String construction uses the is Self Adjoint X1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L470-L470
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L470-L470

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

theorem Lean4LPD.PauliString.isSelfAdjoint_X1 : IsSelfAdjoint X1 := by sorry
