-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerScheduledTraj_within_step
-- name    : Lean4LPD.PauliString.layerScheduledTraj_within_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:35.396167+00:00
-- url     : https://prove2.me/theorems/9c1ed626-2755-41cc-b4f7-d8ab8b3390e1
-- title:
--   Pauli String: layer Scheduled Traj within step
-- statement:
--   Before a boundary, the scheduled execution is the untruncated prefix of the fixed block,
--   started from the scheduled operator at the previous boundary (`apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L183-L195
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L183-L195

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

theorem Lean4LPD.PauliString.layerScheduledTraj_within_step (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d i : ℕ) (hi : i < Γ) :
    layerScheduledTraj layers Γ wstar O (d * Γ + i) =
      layerBlockTraj layers (layerScheduledTraj layers Γ wstar O (d * Γ)) i := by sorry
