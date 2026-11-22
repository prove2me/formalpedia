-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_cls_snd
-- name    : Lean4LPD.PauliString.cls_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:26.576472+00:00
-- url     : https://prove2.me/theorems/dec4b284-0b7d-4a0f-b572-155eadddf028
-- title:
--   Pauli String: cls snd
-- statement:
--   The Pauli String construction uses the cls snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L120-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L120-L120

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

theorem Lean4LPD.PauliString.cls_snd (s : PauliString n) : (cls s).2 = s.z := by sorry

attribute [defeq] Lean4LPD.PauliString.cls_snd
