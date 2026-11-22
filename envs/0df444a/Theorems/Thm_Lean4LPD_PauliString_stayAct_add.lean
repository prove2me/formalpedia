-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_stayAct_add
-- name    : Lean4LPD.PauliString.stayAct_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:25.388844+00:00
-- url     : https://prove2.me/theorems/d0002e36-53db-46a6-9104-673b8eda329a
-- title:
--   Pauli String: stay Act add
-- statement:
--   Additivity of the unchanged branch, supporting finite expansion in
--   `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L129-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L129-L134

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

theorem Lean4LPD.PauliString.stayAct_add (G : PauliString n) (θ : ℝ)
    (y z : EuclideanSpace ℂ (PauliIndex n)) :
    stayAct G θ (y + z) = stayAct G θ y + stayAct G θ z := by sorry
