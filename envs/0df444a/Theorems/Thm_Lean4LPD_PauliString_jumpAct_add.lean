-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_jumpAct_add
-- name    : Lean4LPD.PauliString.jumpAct_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:27.97538+00:00
-- url     : https://prove2.me/theorems/b7600194-e4c5-480b-b5c5-faf08f4ef78b
-- title:
--   Pauli String: jump Act add
-- statement:
--   Additivity of the sine branch, supporting finite expansion in
--   `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L138-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L138-L143

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

theorem Lean4LPD.PauliString.jumpAct_add (G : PauliString n) (θ : ℝ)
    (y z : EuclideanSpace ℂ (PauliIndex n)) :
    jumpAct G θ (y + z) = jumpAct G θ y + jumpAct G θ z := by sorry
