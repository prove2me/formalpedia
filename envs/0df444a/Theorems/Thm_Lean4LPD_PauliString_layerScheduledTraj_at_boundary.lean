-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerScheduledTraj_at_boundary
-- name    : Lean4LPD.PauliString.layerScheduledTraj_at_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:02:54.084805+00:00
-- url     : https://prove2.me/theorems/b9691859-dc62-4a86-94d5-16b665b0072a
-- title:
--   Pauli String: layer Scheduled Traj at boundary
-- statement:
--   **The layer-indexed and the step-indexed executions agree at step boundaries**
--   (`apd:eq:step_component`). Both sides are defined independently, so this is a theorem.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L217-L223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L217-L223

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

theorem Lean4LPD.PauliString.layerScheduledTraj_at_boundary (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hΓ : 0 < Γ) :
    layerScheduledTraj layers Γ wstar O (d * Γ) = layerStepTraj layers Γ wstar O d := by sorry
