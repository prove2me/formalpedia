-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_reachable_subset_reachable_cons
-- name    : Lean4LPD.PauliString.reachable_subset_reachable_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:42.224253+00:00
-- url     : https://prove2.me/theorems/a604522a-c944-4bce-9514-a56f649597e4
-- title:
--   Pauli String: reachable subset reachable cons
-- statement:
--   Enlarging the reachable set of a suffix enlarges it for the whole sequence: the two sequences
--   run the same head layer and only then differ.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L219-L223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L219-L223

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.reachable_subset_reachable_cons {Ls Ls' : List (List (PauliString n))}
    (h : ∀ r : PauliString n, reachable Ls r ⊆ reachable Ls' r) (L : List (PauliString n))
    (p : PauliString n) : reachable (L :: Ls) p ⊆ reachable (L :: Ls') p := by sorry
