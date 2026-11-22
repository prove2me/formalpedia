-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_one_le_weight_of_sympForm_eq_one
-- name    : Lean4LPD.PauliString.one_le_weight_of_sympForm_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:30.577612+00:00
-- url     : https://prove2.me/theorems/eccfcbd2-36d0-4b9d-883b-92f5eda28e0f
-- title:
--   Pauli String: one le weight of symp Form eq one
-- statement:
--   A Pauli string that anticommutes with something is not a phase: it acts on at least one
--   qubit.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L245-L247
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L245-L247

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

theorem Lean4LPD.PauliString.one_le_weight_of_sympForm_eq_one (h : sympForm G s = 1) : 1 ≤ weight G := by sorry
