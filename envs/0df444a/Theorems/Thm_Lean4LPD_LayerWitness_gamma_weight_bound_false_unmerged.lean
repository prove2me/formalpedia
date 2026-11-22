-- Prove2me | Theorems.Thm_Lean4LPD_LayerWitness_gamma_weight_bound_false_unmerged
-- name    : Lean4LPD.LayerWitness.gamma_weight_bound_false_unmerged
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:10:28.340636+00:00
-- url     : https://prove2.me/theorems/66cfba21-8b64-4449-809b-ccd8c64666e3
-- title:
--   Layer Witness: gamma weight bound false unmerged
-- statement:
--   The same combinatorial witness for the literal `2Γ = 4` layers `[L₁, L₂, L₂, L₁]` of the
--   second-order product formula (`apd:eq:suzuki`), with no merging of the two adjacent `H_Γ`
--   half-steps.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L575-L577
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L575-L577

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString

theorem Lean4LPD.LayerWitness.gamma_weight_bound_false_unmerged :
    ∃ q ∈ reachable (layers := [L₁, L₂, L₂, L₁]) (Z 3), 4 < q.weight := by sorry
