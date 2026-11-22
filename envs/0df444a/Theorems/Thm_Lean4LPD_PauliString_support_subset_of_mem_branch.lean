-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_support_subset_of_mem_branch
-- name    : Lean4LPD.PauliString.support_subset_of_mem_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:09:37.766894+00:00
-- url     : https://prove2.me/theorems/a4413849-d84a-4649-af21-0e89ddf77fba
-- title:
--   Pauli String: support subset of mem branch
-- statement:
--   The Pauli String construction uses the support subset of mem branch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L164-L175
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L164-L175

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.support_subset_of_mem_branch (hq : q ∈ branch G p) :
    support q ⊆ support p ∪ support G := by sorry
