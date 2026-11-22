-- Prove2me | Theorems.Thm_Lean4LPD_LayerWitness_gamma_layers_weight_four
-- name    : Lean4LPD.LayerWitness.gamma_layers_weight_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:10:24.918581+00:00
-- url     : https://prove2.me/theorems/1e4a74ea-e9a7-49ec-a893-39a971539bd7
-- title:
--   Layer Witness: gamma layers weight four
-- statement:
--   …and the bound is attained: `P₄` has weight exactly `4` and is reachable in the two brickwork
--   layers. Together with `gamma_layers_weight_le`, the maximum reachable weight after `Γ` layers is
--   exactly `w* k_h^Γ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L545-L547
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L545-L547

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString

theorem Lean4LPD.LayerWitness.gamma_layers_weight_four :
    ∃ q ∈ reachable (layers := [L₁, L₂]) (Z 3), q.weight = 4 := by sorry
