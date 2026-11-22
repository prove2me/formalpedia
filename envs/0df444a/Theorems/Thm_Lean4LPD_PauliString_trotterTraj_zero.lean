-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trotterTraj_zero
-- name    : Lean4LPD.PauliString.trotterTraj_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:35:40.320827+00:00
-- url     : https://prove2.me/theorems/3084c48f-43d2-4ccc-ad8d-15fd75c82ef2
-- title:
--   Pauli String: trotter Traj zero
-- statement:
--   The trajectory starts at the input observable: no truncation is applied before the first
--   rotation (`apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L89-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L89-L91

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

theorem Lean4LPD.PauliString.trotterTraj_zero (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    trotterTraj Gs θ period wstar O 0 = O := by sorry

attribute [defeq] Lean4LPD.PauliString.trotterTraj_zero
