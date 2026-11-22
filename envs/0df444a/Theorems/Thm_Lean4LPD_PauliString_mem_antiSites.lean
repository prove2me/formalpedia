-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
-- name    : Lean4LPD.PauliString.mem_antiSites
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:25.649797+00:00
-- url     : https://prove2.me/theorems/78adebd7-bba2-4a94-9c59-59f3d22edea7
-- title:
--   Pauli String: mem anti Sites
-- statement:
--   The Pauli String construction uses the mem anti Sites property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L163-L165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L163-L165

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

theorem Lean4LPD.PauliString.mem_antiSites :
    i ∈ antiSites G s ↔ site G i ≠ 0 ∧ site s i ≠ 0 ∧ site G i ≠ site s i := by sorry
