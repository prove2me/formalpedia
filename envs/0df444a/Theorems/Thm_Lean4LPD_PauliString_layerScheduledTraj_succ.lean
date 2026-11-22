-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerScheduledTraj_succ
-- name    : Lean4LPD.PauliString.layerScheduledTraj_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:39.069611+00:00
-- url     : https://prove2.me/theorems/61348065-c4fa-4e81-9d7c-f70181f4044e
-- title:
--   Pauli String: layer Scheduled Traj succ
-- statement:
--   A single scheduled layer: conjugation by the layer, then the scheduled projection
--   (`apd:thm:triangle`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L176-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L176-L179

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

theorem Lean4LPD.PauliString.layerScheduledTraj_succ (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (T : ℕ) :
    layerScheduledTraj layers Γ wstar O (T + 1) = truncOp (trotterSchedule Γ wstar T)
      (layerConj (layers (T % Γ)) (layerScheduledTraj layers Γ wstar O T)) := by sorry
