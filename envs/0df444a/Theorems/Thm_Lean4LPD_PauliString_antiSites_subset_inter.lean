-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_antiSites_subset_inter
-- name    : Lean4LPD.PauliString.antiSites_subset_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:35.448332+00:00
-- url     : https://prove2.me/theorems/57b3c453-fd8c-4265-96d5-a91a66bda6c9
-- title:
--   Pauli String: anti Sites subset inter
-- statement:
--   A locally anticommuting site lies in both supports.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L114-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L114-L118

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.antiSites_subset_inter (G s : PauliString n) :
    antiSites G s ⊆ support G ∩ support s := by sorry
