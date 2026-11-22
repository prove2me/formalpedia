-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_antiLayer_partner
-- name    : Lean4LPD.PauliString.antiLayer_partner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:45.952986+00:00
-- url     : https://prove2.me/theorems/8e2917cf-971e-47fd-a231-b36f322759a8
-- title:
--   Pauli String: anti Layer partner
-- statement:
--   Taking any generator in a commuting layer leaves the entire anticommutation set unchanged.
--   Supporting lemma for `apd:thm:layer_inflow`. Disjointness is a sufficient
--   condition, but pairwise commutation is exactly what this identity needs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L386-L393
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L386-L393

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

theorem Lean4LPD.PauliString.antiLayer_partner (L : List (PauliString n)) (H : PauliString n)
    (hH : ∀ G ∈ L, sympForm G H = 0) (p : PauliIndex n) :
    antiLayer L (partner H p) = antiLayer L p := by sorry
