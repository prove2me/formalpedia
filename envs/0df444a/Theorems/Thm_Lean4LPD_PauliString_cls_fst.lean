-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_cls_fst
-- name    : Lean4LPD.PauliString.cls_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:28.134467+00:00
-- url     : https://prove2.me/theorems/89470397-b3be-4b98-9685-bd61e5595e27
-- title:
--   Pauli String: cls fst
-- statement:
--   The Pauli String construction uses the cls fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L118-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L118-L118

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

theorem Lean4LPD.PauliString.cls_fst (s : PauliString n) : (cls s).1 = s.x := by sorry

attribute [defeq] Lean4LPD.PauliString.cls_fst
