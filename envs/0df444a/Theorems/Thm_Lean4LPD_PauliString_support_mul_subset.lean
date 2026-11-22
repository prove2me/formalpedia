-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_support_mul_subset
-- name    : Lean4LPD.PauliString.support_mul_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:24.78653+00:00
-- url     : https://prove2.me/theorems/7c4931b7-32d6-4e37-8830-d3e8e09d60ea
-- title:
--   Pauli String: support mul subset
-- statement:
--   The support of a product is contained in the union of the supports.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L99-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L99-L107

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.support_mul_subset (s t : PauliString n) :
    support (s * t) ⊆ support s ∪ support t := by sorry
