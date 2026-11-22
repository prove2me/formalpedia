-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_reachable_nil
-- name    : Lean4LPD.PauliString.reachable_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:50.167331+00:00
-- url     : https://prove2.me/theorems/bd722f59-fcf2-403b-b400-8d54b59400e4
-- title:
--   Pauli String: reachable nil
-- statement:
--   The Pauli String construction uses the reachable nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L197-L197
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L197-L197

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.reachable_nil (p : PauliString n) : reachable [] p = {p} := by sorry

attribute [defeq] Lean4LPD.PauliString.reachable_nil
