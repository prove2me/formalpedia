-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_self_mem_branch
-- name    : Lean4LPD.PauliString.self_mem_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:39.493988+00:00
-- url     : https://prove2.me/theorems/c5cbb473-86cc-4185-acc1-4888c2575661
-- title:
--   Pauli String: self mem branch
-- statement:
--   The Pauli String construction uses the self mem branch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L157-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L157-L158

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.self_mem_branch (G p : PauliString n) : p ∈ branch G p := by sorry
