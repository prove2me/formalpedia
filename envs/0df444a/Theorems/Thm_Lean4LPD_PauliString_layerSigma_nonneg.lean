-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerSigma_nonneg
-- name    : Lean4LPD.PauliString.layerSigma_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:25.118832+00:00
-- url     : https://prove2.me/theorems/89925fdd-2c3d-4dba-8cc0-edcf0cc61a8f
-- title:
--   Pauli String: layer Sigma nonneg
-- statement:
--   The layer's largest absolute sine is nonnegative; supporting lemma for
--   `apd:thm:layer_inflow` with the parameter `σ = layerSigma L`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L404-L407
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L404-L407

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

theorem Lean4LPD.PauliString.layerSigma_nonneg (L : List (PauliString n × ℝ)) : 0 ≤ layerSigma L := by sorry
