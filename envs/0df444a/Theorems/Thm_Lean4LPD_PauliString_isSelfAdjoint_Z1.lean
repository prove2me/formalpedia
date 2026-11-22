-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_Z1
-- name    : Lean4LPD.PauliString.isSelfAdjoint_Z1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:08:27.075833+00:00
-- url     : https://prove2.me/theorems/3a024abc-05de-4de4-958c-fd154a9110c7
-- title:
--   Pauli String: is Self Adjoint Z1
-- statement:
--   The Pauli String construction uses the is Self Adjoint Z1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L472-L472
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L472-L472

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

theorem Lean4LPD.PauliString.isSelfAdjoint_Z1 : IsSelfAdjoint Z1 := by sorry
