-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_herm_z
-- name    : Lean4LPD.PauliString.herm_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:25.627855+00:00
-- url     : https://prove2.me/theorems/119df7b2-9b2b-48d7-8ef4-a9b15bfadad3
-- title:
--   Pauli String: herm z
-- statement:
--   The Pauli String construction uses the herm z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L129-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L129-L129

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.herm_z (p : PauliIndex n) : (herm p).z = p.2 := by sorry

attribute [defeq] Lean4LPD.PauliString.herm_z
