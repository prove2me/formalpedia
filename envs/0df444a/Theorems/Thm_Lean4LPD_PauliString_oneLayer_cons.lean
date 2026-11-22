-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_oneLayer_cons
-- name    : Lean4LPD.PauliString.oneLayer_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:42.750726+00:00
-- url     : https://prove2.me/theorems/b1d8ea12-0f7b-49d8-b367-1f897dc051a4
-- title:
--   Pauli String: one Layer cons
-- statement:
--   The Pauli String construction uses the one Layer cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L186-L188
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L186-L188

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.oneLayer_cons (G : PauliString n) (Gs : List (PauliString n))
    (p : PauliString n) :
    oneLayer (G :: Gs) p = (branch G p).biUnion (oneLayer Gs) := by sorry

attribute [defeq] Lean4LPD.PauliString.oneLayer_cons
