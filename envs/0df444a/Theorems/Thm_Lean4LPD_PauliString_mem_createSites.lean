-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_mem_createSites
-- name    : Lean4LPD.PauliString.mem_createSites
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:22.269801+00:00
-- url     : https://prove2.me/theorems/7078c5b7-d940-4787-93f4-e88871352c41
-- title:
--   Pauli String: mem create Sites
-- statement:
--   The Pauli String construction uses the mem create Sites property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L151-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L151-L161

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

theorem Lean4LPD.PauliString.mem_createSites : i ∈ createSites G s ↔ site G i ≠ 0 ∧ site s i = 0 := by sorry
