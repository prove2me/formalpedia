-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_highNorm_trotterStepTraj_succ
-- name    : Lean4LPD.PauliString.highNorm_trotterStepTraj_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:30.065164+00:00
-- url     : https://prove2.me/theorems/0a36ab2c-3cdc-4384-b69a-365d80c29a6a
-- title:
--   Pauli String: high Norm trotter Step Traj succ
-- statement:
--   The retained operator has zero high-weight mass after each completed step. This is a
--   support theorem, not an error bound (`apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L198-L201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L198-L201

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

theorem Lean4LPD.PauliString.highNorm_trotterStepTraj_succ (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    highNorm wstar (trotterStepTraj Gs θ period wstar O (d + 1)) = 0 := by sorry
