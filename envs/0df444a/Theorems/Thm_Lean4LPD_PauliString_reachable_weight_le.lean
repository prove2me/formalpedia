-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_reachable_weight_le
-- name    : Lean4LPD.PauliString.reachable_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:52.341799+00:00
-- url     : https://prove2.me/theorems/6724e994-f4f3-4697-9c37-e77f2a956aa9
-- title:
--   Pauli String: reachable weight le
-- statement:
--   **The `L`-fold iterate**, `|q| ≤ k_h^L |p|` after `L` layers.
--
--   With `|p| ≤ w*` and `L = ΥΓ`, the number of layers of one Trotter step of the `p`th-order formula
--   `apd:eq:suzuki`, the right-hand side is at most `w* k_h^{ΥΓ}`, the weight bound of
--   `apd:thm:lightcone` for the Pauli strings of the discarded component `apd:eq:step_component`.
--   Nothing is assumed about how the layers are related: they may repeat, as they do in a
--   second-order step.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L411-L432
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L411-L432

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.reachable_weight_le : ∀ {Ls : List (List (PauliString n))},
    (∀ L ∈ Ls, IsLayer kh L) → 1 ≤ kh →
    ∀ {p q : PauliString n}, q ∈ reachable Ls p → weight q ≤ kh ^ Ls.length * weight p := by sorry
