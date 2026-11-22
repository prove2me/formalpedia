-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_highNorm_layerStepTraj_succ
-- name    : Lean4LPD.PauliString.highNorm_layerStepTraj_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:02:45.264369+00:00
-- url     : https://prove2.me/theorems/8358a3fe-8206-4f03-8a92-dec312c76b4c
-- title:
--   Pauli String: high Norm layer Step Traj succ
-- statement:
--   After every completed step the kept operator has no mass above the cutoff. This gives the
--   reset condition in `apd:eq:total_high_weight_norm`. It is a statement about the kept operator,
--   not about the discarded one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L254-L257
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L254-L257

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

theorem Lean4LPD.PauliString.highNorm_layerStepTraj_succ (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    highNorm wstar (layerStepTraj layers Γ wstar O (d + 1)) = 0 := by sorry
