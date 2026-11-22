-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_norm_layerAct
-- name    : Lean4LPD.PauliString.norm_layerAct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:29.483664+00:00
-- url     : https://prove2.me/theorems/39847e29-8083-4f69-805e-75a7193d3af5
-- title:
--   Pauli String: norm layer Act
-- statement:
--   A finite layer of Hermitian generators preserves the coefficient `ℓ²` norm. This gives the
--   contraction of the diagonal (high-to-high) block; the off-diagonal block is handled by the Schur
--   bound of `apd:thm:layer_inflow` below.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L188-L196
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L188-L196

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

theorem Lean4LPD.PauliString.norm_layerAct (L : List (PauliString n × ℝ))
    (hL : ∀ g ∈ L, IsSelfAdjoint g.1) (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖layerAct L y‖ = ‖y‖ := by sorry
