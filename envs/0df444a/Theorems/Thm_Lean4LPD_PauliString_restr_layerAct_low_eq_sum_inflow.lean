-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_restr_layerAct_low_eq_sum_inflow
-- name    : Lean4LPD.PauliString.restr_layerAct_low_eq_sum_inflow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:26.6148+00:00
-- url     : https://prove2.me/theorems/4392bc77-93dc-47c1-8095-ea3030d18584
-- title:
--   Pauli String: restr layer Act low eq sum inflow
-- statement:
--   **The high-from-low block of a layer is the sum of its exactly-`j` blocks.**
--   This is the action form of `A_RB = ∑_{j≥1} A^{(j)}` in `apd:thm:layer_inflow`. The finite sum
--   runs over `0 ≤ j ≤ L.length`; its `j = 0` term vanishes by `layerInflowMatrix_zero`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L909-L916
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L909-L916

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

theorem Lean4LPD.PauliString.restr_layerAct_low_eq_sum_inflow (L : List (PauliString n × ℝ)) (w : ℕ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    restr (highSet n w) (layerAct L (restr (highSet n w)ᶜ y))
      = ∑ j ∈ range (L.length + 1), Lean4LPD.clm (layerInflowMatrix L w j) y := by sorry
