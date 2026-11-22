-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_support_subset_cover_of_mem_hitting
-- name    : Lean4LPD.PauliString.support_subset_cover_of_mem_hitting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:43.697441+00:00
-- url     : https://prove2.me/theorems/dfd6aeb2-529b-42e6-9c8f-09daea68f704
-- title:
--   Pauli String: support subset cover of mem hitting
-- statement:
--   The Pauli String construction uses the support subset cover of mem hitting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L279-L281
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L279-L281

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.support_subset_cover_of_mem_hitting (h : G ∈ hitting L S) :
    support G ⊆ cover L S := by sorry
