-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerBlockTraj_eq_scheduled_prefix
-- name    : Lean4LPD.PauliString.layerBlockTraj_eq_scheduled_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:16.668609+00:00
-- url     : https://prove2.me/theorems/c95b7524-6514-46a9-8398-3e9a8a900244
-- title:
--   Pauli String: layer Block Traj eq scheduled prefix
-- statement:
--   Inside a step, the untruncated prefix of the block equals the scheduled trajectory at the
--   corresponding layer. This identification lets the rung masses of `pauliMultiLadder` be used in
--   `apd:eq:total_high_weight_norm`. The endpoint `i = Γ` is excluded: there the scheduled
--   trajectory has already been cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L229-L234
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L229-L234

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}

theorem Lean4LPD.PauliString.layerBlockTraj_eq_scheduled_prefix (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d i : ℕ) (hi : i < Γ) :
    layerBlockTraj layers (layerStepTraj layers Γ wstar O d) i =
      layerScheduledTraj layers Γ wstar O (d * Γ + i) := by sorry
