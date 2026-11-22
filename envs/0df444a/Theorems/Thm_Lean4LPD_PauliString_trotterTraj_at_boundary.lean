-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trotterTraj_at_boundary
-- name    : Lean4LPD.PauliString.trotterTraj_at_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:36:15.99865+00:00
-- url     : https://prove2.me/theorems/d1eb3840-2b26-48bb-8224-d0ef1670f3b9
-- title:
--   Pauli String: trotter Traj at boundary
-- statement:
--   The rotation-indexed execution agrees with the independently defined step recurrence
--   at every boundary (`apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L162-L169
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L162-L169

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

theorem Lean4LPD.PauliString.trotterTraj_at_boundary (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hp : 0 < period) :
    trotterTraj Gs θ period wstar O (d * period) =
      trotterStepTraj Gs θ period wstar O d := by sorry
