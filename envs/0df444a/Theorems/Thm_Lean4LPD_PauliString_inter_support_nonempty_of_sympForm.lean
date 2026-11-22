-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_inter_support_nonempty_of_sympForm
-- name    : Lean4LPD.PauliString.inter_support_nonempty_of_sympForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:23.824986+00:00
-- url     : https://prove2.me/theorems/27c4d4ed-2c28-43c4-8bd6-582496680837
-- title:
--   Pauli String: inter support nonempty of symp Form
-- statement:
--   Contrapositive of the previous theorem, in the form the light-cone count consumes: a generator
--   that anticommutes with `p` must touch `p`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L135-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L135-L138

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.inter_support_nonempty_of_sympForm (h : sympForm G p = 1) :
    (support G ∩ support p).Nonempty := by sorry
