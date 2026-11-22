-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trotterBlock_eq_boundary_pre
-- name    : Lean4LPD.PauliString.trotterBlock_eq_boundary_pre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:15.614864+00:00
-- url     : https://prove2.me/theorems/e8d0a7c0-92c5-49d7-85c3-124dd64fc0a5
-- title:
--   Pauli String: trotter Block eq boundary pre
-- statement:
--   The pre-truncation operator of a block is the last rotation of the block applied to the
--   scheduled trajectory just before the boundary (`apd:eq:step_component`). This connects the
--   step-indexed recurrence to the rotation-indexed local flow of `Truncate.lean`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L206-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L206-L216

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

theorem Lean4LPD.PauliString.trotterBlock_eq_boundary_pre (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hp : 0 < period) :
    traj Gs θ (trotterStepTraj Gs θ period wstar O d) period =
      rot (toMatrix (Gs (period - 1))) (θ (period - 1)) *
        trotterTraj Gs θ period wstar O (d * period + (period - 1)) *
        rot (toMatrix (Gs (period - 1))) (-(θ (period - 1))) := by sorry
