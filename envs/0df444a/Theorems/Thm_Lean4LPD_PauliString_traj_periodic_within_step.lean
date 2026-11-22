-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_traj_periodic_within_step
-- name    : Lean4LPD.PauliString.traj_periodic_within_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:56.708446+00:00
-- url     : https://prove2.me/theorems/192d0553-d400-4a58-b43f-c5e4455223a6
-- title:
--   Pauli String: traj periodic within step
-- statement:
--   The untruncated, modulo-indexed run executes the specified block between successive
--   boundaries, as used in `apd:thm:triangle`. The endpoint `i = period` is
--   included. No positivity assumption is needed; `period = 0` admits only `i = 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L163-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L163-L174

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}

theorem Lean4LPD.PauliString.traj_periodic_within_step (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d i : ℕ) (hi : i ≤ period) :
    traj (fun g => Gs (g % period)) (fun g => θ (g % period)) O (d * period + i) =
      traj Gs θ
        (traj (fun g => Gs (g % period)) (fun g => θ (g % period)) O (d * period)) i := by sorry
