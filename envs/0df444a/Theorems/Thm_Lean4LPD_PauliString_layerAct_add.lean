-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerAct_add
-- name    : Lean4LPD.PauliString.layerAct_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:19.562584+00:00
-- url     : https://prove2.me/theorems/ea774bd4-3ef6-4f19-aff8-ee32b44d8122
-- title:
--   Pauli String: layer Act add
-- statement:
--   Additivity of the layer action on coefficient vectors. Supporting lemma for the high/low
--   split in `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L886-L894
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L886-L894

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

theorem Lean4LPD.PauliString.layerAct_add (L : List (PauliString n × ℝ))
    (y z : EuclideanSpace ℂ (PauliIndex n)) :
    layerAct L (y + z) = layerAct L y + layerAct L z := by sorry
