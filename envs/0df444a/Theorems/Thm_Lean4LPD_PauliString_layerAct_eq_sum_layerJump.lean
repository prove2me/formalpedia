-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerAct_eq_sum_layerJump
-- name    : Lean4LPD.PauliString.layerAct_eq_sum_layerJump
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:09.259135+00:00
-- url     : https://prove2.me/theorems/3a15ebf0-7387-4815-9537-2fdd16cfba9c
-- title:
--   Pauli String: layer Act eq sum layer Jump
-- statement:
--   **Expansion of a layer by number of sine branches.** `layerAct L` is the finite sum of its
--   exactly-`j` components, `0 ≤ j ≤ L.length`; this is the expansion used in
--   `apd:thm:layer_inflow`. It is an identity for arbitrary ordered lists of rotations: disjointness
--   and commutation are needed only for the binomial counting estimates below.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L250-L267
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L250-L267

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

theorem Lean4LPD.PauliString.layerAct_eq_sum_layerJump (L : List (PauliString n × ℝ))
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    layerAct L y = ∑ j ∈ range (L.length + 1), layerJump L j y := by sorry
