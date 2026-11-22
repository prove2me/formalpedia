-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_periodic_traj_sub_trotterStepTraj
-- name    : Lean4LPD.PauliString.periodic_traj_sub_trotterStepTraj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:45:43.640914+00:00
-- url     : https://prove2.me/theorems/97521699-dcb5-4e1b-805c-cb68d2071ff1
-- title:
--   Pauli String: periodic traj sub trotter Step Traj
-- statement:
--   The operator telescope of `apd:thm:triangle`, entirely in terms of
--   the rotation-indexed `traj`, the kept trajectory `trotterStepTraj` and the discarded operators
--   `discardedStep`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L193-L200
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L193-L200

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

theorem Lean4LPD.PauliString.periodic_traj_sub_trotterStepTraj (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    traj (fun g => Gs (g % period)) (fun g => θ (g % period)) O (r * period) -
        trotterStepTraj Gs θ period wstar O r =
      ∑ d ∈ range r, traj (fun g => Gs (g % period)) (fun g => θ (g % period))
        (discardedStep Gs θ period wstar O d) ((r - 1 - d) * period) := by sorry
