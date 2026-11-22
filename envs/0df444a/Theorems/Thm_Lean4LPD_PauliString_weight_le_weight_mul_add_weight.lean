-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_weight_le_weight_mul_add_weight
-- name    : Lean4LPD.PauliString.weight_le_weight_mul_add_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:09:09.578028+00:00
-- url     : https://prove2.me/theorems/adbd95ec-9ff2-43bf-8046-596c71b2ebe5
-- title:
--   Pauli String: weight le weight mul add weight
-- statement:
--   The companion lower bound, again with no hypothesis.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L259-L263
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L259-L263

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

theorem Lean4LPD.PauliString.weight_le_weight_mul_add_weight (G s : PauliString n) :
    weight s ≤ weight (G * s) + weight G := by sorry
