-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_zero_of_disjoint_support
-- name    : Lean4LPD.PauliString.sympForm_eq_zero_of_disjoint_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:38.196332+00:00
-- url     : https://prove2.me/theorems/b40a6295-8400-41f4-819d-bdd399c7d393
-- title:
--   Pauli String: symp Form eq zero of disjoint support
-- statement:
--   **Pauli strings with disjoint supports commute.** This is what makes a layer a layer: the
--   generators of one disjoint-support layer of `apd:thm:lightcone` commute with each other, so the
--   layer is a product of commuting Pauli rotations.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L123-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L123-L131

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.sympForm_eq_zero_of_disjoint_support (h : Disjoint (support G) (support p)) :
    sympForm G p = 0 := by sorry
