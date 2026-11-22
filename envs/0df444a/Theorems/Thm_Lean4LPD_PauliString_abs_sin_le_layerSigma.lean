-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_abs_sin_le_layerSigma
-- name    : Lean4LPD.PauliString.abs_sin_le_layerSigma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:21.827149+00:00
-- url     : https://prove2.me/theorems/98e5505b-8330-4209-b945-0bf1e75fb4d9
-- title:
--   Pauli String: abs sin le layer Sigma
-- statement:
--   Every individual sine magnitude is bounded by the layer parameter.
--   Supporting lemma for `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L411-L418
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L411-L418

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

theorem Lean4LPD.PauliString.abs_sin_le_layerSigma (L : List (PauliString n × ℝ))
    (g : PauliString n × ℝ) (hg : g ∈ L) : |Real.sin g.2| ≤ layerSigma L := by sorry
