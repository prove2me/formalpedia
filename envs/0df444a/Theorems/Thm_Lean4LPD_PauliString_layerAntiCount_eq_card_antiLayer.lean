-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerAntiCount_eq_card_antiLayer
-- name    : Lean4LPD.PauliString.layerAntiCount_eq_card_antiLayer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:59.654087+00:00
-- url     : https://prove2.me/theorems/e5e905e2-fd32-43a0-b6f6-5e2ae0aadf9a
-- title:
--   Pauli String: layer Anti Count eq card anti Layer
-- statement:
--   In a disjoint layer the list count has no anticommuting duplicates, so it is exactly the
--   finite-set cardinality `|𝒜(p)|`. Supporting lemma for `apd:thm:layer_inflow`.
--   Repeated scalar generators are harmless because they never anticommute.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L559-L574
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L559-L574

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

theorem Lean4LPD.PauliString.layerAntiCount_eq_card_antiLayer (L : List (PauliString n)) {kh : ℕ}
    (hL : IsLayer kh L) (p : PauliIndex n) :
    layerAntiCount L p = (antiLayer L p).card := by sorry
