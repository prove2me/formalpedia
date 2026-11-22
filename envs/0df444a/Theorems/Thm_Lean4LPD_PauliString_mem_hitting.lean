-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_mem_hitting
-- name    : Lean4LPD.PauliString.mem_hitting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:36.441388+00:00
-- url     : https://prove2.me/theorems/003f1fb0-c2f3-4be0-b5eb-653315ae3ec6
-- title:
--   Pauli String: mem hitting
-- statement:
--   The Pauli String construction uses the mem hitting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L266-L267
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L266-L267

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.mem_hitting : G ∈ hitting L S ↔ G ∈ L ∧ (support G ∩ S).Nonempty := by sorry
