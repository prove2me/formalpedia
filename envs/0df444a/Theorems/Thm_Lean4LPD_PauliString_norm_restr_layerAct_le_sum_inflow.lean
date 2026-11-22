-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_norm_restr_layerAct_le_sum_inflow
-- name    : Lean4LPD.PauliString.norm_restr_layerAct_le_sum_inflow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:18.139804+00:00
-- url     : https://prove2.me/theorems/fd701abc-139f-44d6-98f5-9224005bb3ff
-- title:
--   Pauli String: norm restr layer Act le sum inflow
-- statement:
--   **High-weight norm after a layer: the previous high-weight norm plus the inflows.**
--   The triangle inequality applied to the block decomposition of `apd:thm:layer_inflow`: the
--   high-to-high block is a contraction because the layer is an isometry (`norm_layerAct`), and the
--   high-from-low block is the sum of the `A^{(j)}`. Both facts are proved above from the rotations,
--   so no flow inequality is assumed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L923-L937
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L923-L937

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

theorem Lean4LPD.PauliString.norm_restr_layerAct_le_sum_inflow (L : List (PauliString n × ℝ))
    (hL : ∀ g ∈ L, IsSelfAdjoint g.1) (w : ℕ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖restr (highSet n w) (layerAct L y)‖ ≤ ‖restr (highSet n w) y‖
      + ∑ j ∈ range (L.length + 1), ‖Lean4LPD.clm (layerInflowMatrix L w j) y‖ := by sorry
