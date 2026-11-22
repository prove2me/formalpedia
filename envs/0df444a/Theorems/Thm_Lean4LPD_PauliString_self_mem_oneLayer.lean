-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_self_mem_oneLayer
-- name    : Lean4LPD.PauliString.self_mem_oneLayer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:41.028785+00:00
-- url     : https://prove2.me/theorems/0b19fbcc-94b4-4e82-91ef-8cc88859c2b3
-- title:
--   Pauli String: self mem one Layer
-- statement:
--   A string can always sit out a layer: every generator's `branch` retains its input, so `p`
--   itself survives the whole layer unbranched.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L205-L208
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L205-L208

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.self_mem_oneLayer (L : List (PauliString n)) (p : PauliString n) : p ∈ oneLayer L p := by sorry
