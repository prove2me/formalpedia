-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_reachable_subset_cons
-- name    : Lean4LPD.PauliString.reachable_subset_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:40.172405+00:00
-- url     : https://prove2.me/theorems/d3331368-cab7-4e8e-8ff5-2d0fcecc3712
-- title:
--   Pauli String: reachable subset cons
-- statement:
--   **Inserting a layer only enlarges the reachable set**, by `self_mem_oneLayer`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L211-L215
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L211-L215

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.reachable_subset_cons (L : List (PauliString n)) (Ls : List (List (PauliString n)))
    (p : PauliString n) : reachable Ls p ⊆ reachable (L :: Ls) p := by sorry
