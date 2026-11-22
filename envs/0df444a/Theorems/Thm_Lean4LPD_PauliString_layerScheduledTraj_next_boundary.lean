-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerScheduledTraj_next_boundary
-- name    : Lean4LPD.PauliString.layerScheduledTraj_next_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:42.519653+00:00
-- url     : https://prove2.me/theorems/ebf9f19d-3a0a-4392-9e9d-dac0cecfd885
-- title:
--   Pauli String: layer Scheduled Traj next boundary
-- statement:
--   Over one full block, the scheduled execution evolves without truncation and is then cut
--   (`apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L199-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L199-L213

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

theorem Lean4LPD.PauliString.layerScheduledTraj_next_boundary (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hΓ : 0 < Γ) :
    layerScheduledTraj layers Γ wstar O ((d + 1) * Γ) = truncOp (highSet n wstar)ᶜ
      (layerBlockTraj layers (layerScheduledTraj layers Γ wstar O (d * Γ)) Γ) := by sorry
