-- Prove2me | Theorems.Thm_Lean4LPD_LayerWitness_gamma_layers_weight_le
-- name    : Lean4LPD.LayerWitness.gamma_layers_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:10:07.446259+00:00
-- url     : https://prove2.me/theorems/c8bd26e6-7c79-47ec-a140-4446e7f89977
-- title:
--   Layer Witness: gamma layers weight le
-- statement:
--   **After `Γ` layers the weight is at most `w* k_h^Γ`.** With `w* = 1`, `k_h = 2` and the
--   `Γ = 2` brickwork layers `[L₁, L₂]`, nothing of weight more than `w* k_h^Γ = 4` is reachable from
--   `Z₃`. By `gamma_layers_weight_four` the value `4` is attained, so the bound `k_h ^ L` has no slack
--   in its constant: the weight-`6` string of `gamma_weight_bound_false` exceeds `4` only because a
--   second-order step has more than `Γ` layers.
--
--   Nothing about the brickwork is used: this is `reachable_weight_le` at `k_h = 2` and two layers.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L491-L500
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L491-L500

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString

theorem Lean4LPD.LayerWitness.gamma_layers_weight_le :
    ∀ q ∈ reachable (layers := [L₁, L₂]) (Z 3), q.weight ≤ 4 := by sorry
