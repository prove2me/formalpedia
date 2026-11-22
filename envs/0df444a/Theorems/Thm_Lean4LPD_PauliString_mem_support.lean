-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_mem_support
-- name    : Lean4LPD.PauliString.mem_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:21.213449+00:00
-- url     : https://prove2.me/theorems/86172a54-8f5c-43fb-80ab-f8c453c9cda4
-- title:
--   Pauli String: mem support
-- statement:
--   The Pauli String construction uses the mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L116-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L116-L116

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}

theorem Lean4LPD.PauliString.mem_support : i ∈ support s ↔ site s i ≠ 0 := by sorry
