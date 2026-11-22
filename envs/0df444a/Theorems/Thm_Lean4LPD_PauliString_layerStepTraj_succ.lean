-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerStepTraj_succ
-- name    : Lean4LPD.PauliString.layerStepTraj_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:02:33.08422+00:00
-- url     : https://prove2.me/theorems/b9989bb8-3426-4169-a5b7-1870f38a0a41
-- title:
--   Pauli String: layer Step Traj succ
-- statement:
--   One complete step: evolve through the block, then cut (`apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L157-L160
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L157-L160

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

theorem Lean4LPD.PauliString.layerStepTraj_succ (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    layerStepTraj layers Γ wstar O (d + 1) = truncOp (highSet n wstar)ᶜ
      (layerBlockTraj layers (layerStepTraj layers Γ wstar O d) Γ) := by sorry
