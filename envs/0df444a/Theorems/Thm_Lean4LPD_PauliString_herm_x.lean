-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_herm_x
-- name    : Lean4LPD.PauliString.herm_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:25.239188+00:00
-- url     : https://prove2.me/theorems/40ed1b6b-68c4-45d8-9829-4accb5aaa479
-- title:
--   Pauli String: herm x
-- statement:
--   The Pauli String construction uses the herm x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L127-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L127-L127

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

theorem Lean4LPD.PauliString.herm_x (p : PauliIndex n) : (herm p).x = p.1 := by sorry

attribute [defeq] Lean4LPD.PauliString.herm_x
