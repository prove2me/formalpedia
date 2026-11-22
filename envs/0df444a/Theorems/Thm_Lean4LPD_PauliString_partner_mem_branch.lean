-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_partner_mem_branch
-- name    : Lean4LPD.PauliString.partner_mem_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:09:36.558737+00:00
-- url     : https://prove2.me/theorems/461688fd-c119-4487-9afc-f5418394d1e0
-- title:
--   Pauli String: partner mem branch
-- statement:
--   The anticommuting branch: the partner `i G p` is reachable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L161-L162
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L161-L162

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.partner_mem_branch (h : sympForm G p = 1) : phaseMul 1 (G * p) ∈ branch G p := by sorry
