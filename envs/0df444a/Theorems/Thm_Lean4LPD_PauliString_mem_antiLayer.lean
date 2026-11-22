-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_mem_antiLayer
-- name    : Lean4LPD.PauliString.mem_antiLayer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:07.8709+00:00
-- url     : https://prove2.me/theorems/14e6f193-28a3-4ce5-92be-ce6c86c3955e
-- title:
--   Pauli String: mem anti Layer
-- statement:
--   Membership in the layer's anticommuting generator set; supporting lemma for
--   `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L331-L333
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L331-L333

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

theorem Lean4LPD.PauliString.mem_antiLayer (L : List (PauliString n)) (p : PauliIndex n)
    (G : PauliString n) : G ∈ antiLayer L p ↔ G ∈ L ∧ sympForm G (herm p) = 1 := by sorry
