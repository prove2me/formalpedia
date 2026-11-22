-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_weight_one
-- name    : Lean4LPD.PauliString.weight_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:21.753375+00:00
-- url     : https://prove2.me/theorems/6173c5e7-a5e8-43fd-afdf-96852adc1dfd
-- title:
--   Pauli String: weight one
-- statement:
--   The Pauli String construction uses the weight one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L122-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L122-L123

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

theorem Lean4LPD.PauliString.weight_one : weight (1 : PauliString n) = 0 := by sorry
