-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_oneLayer_nil
-- name    : Lean4LPD.PauliString.oneLayer_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:40.527607+00:00
-- url     : https://prove2.me/theorems/bba15cf2-1f8b-429e-b455-7a86c9ad22b4
-- title:
--   Pauli String: one Layer nil
-- statement:
--   The Pauli String construction uses the one Layer nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L184-L184
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L184-L184

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.oneLayer_nil (p : PauliString n) : oneLayer [] p = {p} := by sorry

attribute [defeq] Lean4LPD.PauliString.oneLayer_nil
