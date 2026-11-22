-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layer_sympForm_eq_zero
-- name    : Lean4LPD.PauliString.layer_sympForm_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:42.201386+00:00
-- url     : https://prove2.me/theorems/eb16aadb-ec97-471c-8034-0f06fd69e96c
-- title:
--   Pauli String: layer symp Form eq zero
-- statement:
--   Disjoint supports imply the pairwise commutation used by the exactly-`j` row and column
--   estimates. Supporting lemma for `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L735-L742
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L735-L742

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

theorem Lean4LPD.PauliString.layer_sympForm_eq_zero (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) :
    ∀ g ∈ L, ∀ h ∈ L, sympForm g.1 h.1 = 0 := by sorry
