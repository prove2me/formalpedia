-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trotterStepTraj_zero
-- name    : Lean4LPD.PauliString.trotterStepTraj_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:35:20.966068+00:00
-- url     : https://prove2.me/theorems/b9b6b81c-e1e6-40e1-9279-08a673e20daf
-- title:
--   Pauli String: trotter Step Traj zero
-- statement:
--   The step-indexed recurrence starts at the input observable itself
--   (`apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L113-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L113-L115

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}

theorem Lean4LPD.PauliString.trotterStepTraj_zero (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    trotterStepTraj Gs θ period wstar O 0 = O := by sorry

attribute [defeq] Lean4LPD.PauliString.trotterStepTraj_zero
