-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_cls_herm
-- name    : Lean4LPD.PauliString.cls_herm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:30.345175+00:00
-- url     : https://prove2.me/theorems/6bcd557f-16a7-43ed-9a67-b0e16d90a090
-- title:
--   Pauli String: cls herm
-- statement:
--   The Pauli String construction uses the cls herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L131-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L131-L131

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

theorem Lean4LPD.PauliString.cls_herm (p : PauliIndex n) : cls (herm p) = p := by sorry

attribute [defeq] Lean4LPD.PauliString.cls_herm
