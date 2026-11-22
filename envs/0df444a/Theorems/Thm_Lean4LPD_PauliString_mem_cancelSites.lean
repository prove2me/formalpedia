-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_mem_cancelSites
-- name    : Lean4LPD.PauliString.mem_cancelSites
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:09.187053+00:00
-- url     : https://prove2.me/theorems/f459f68b-2adb-41df-b5b9-f653d1382371
-- title:
--   Pauli String: mem cancel Sites
-- statement:
--   The Pauli String construction uses the mem cancel Sites property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L147-L149
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L147-L149

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

theorem Lean4LPD.PauliString.mem_cancelSites : i ∈ cancelSites G s ↔ site s i ≠ 0 ∧ site G i = site s i := by sorry
