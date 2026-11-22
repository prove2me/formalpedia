-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_hitting_subset_cons
-- name    : Lean4LPD.PauliString.hitting_subset_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:45.098576+00:00
-- url     : https://prove2.me/theorems/95f0eb02-7198-47d1-a4ce-1dd178d423e1
-- title:
--   Pauli String: hitting subset cons
-- statement:
--   The Pauli String construction uses the hitting subset cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L283-L287
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L283-L287

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.hitting_subset_cons (G : PauliString n) (Gs : List (PauliString n))
    (S : Finset (Fin n)) : hitting Gs S ⊆ hitting (G :: Gs) S := by sorry
