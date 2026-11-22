-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_reachable_cons
-- name    : Lean4LPD.PauliString.reachable_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:43.232082+00:00
-- url     : https://prove2.me/theorems/660cb8a4-2442-4d03-84d1-9094664d7c79
-- title:
--   Pauli String: reachable cons
-- statement:
--   The Pauli String construction uses the reachable cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L199-L201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L199-L201

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.reachable_cons (L : List (PauliString n)) (Ls : List (List (PauliString n)))
    (p : PauliString n) :
    reachable (L :: Ls) p = (oneLayer L p).biUnion (reachable Ls) := by sorry

attribute [defeq] Lean4LPD.PauliString.reachable_cons
