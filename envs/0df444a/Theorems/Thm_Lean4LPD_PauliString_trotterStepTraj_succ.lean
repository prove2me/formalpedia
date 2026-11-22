-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trotterStepTraj_succ
-- name    : Lean4LPD.PauliString.trotterStepTraj_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:36:17.816074+00:00
-- url     : https://prove2.me/theorems/0238f8f3-45e8-4808-a87e-c3eced59278e
-- title:
--   Pauli String: trotter Step Traj succ
-- statement:
--   The recurrence of the kept operator: evolve through the whole block, then cut
--   (`apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L119-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L119-L123

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

theorem Lean4LPD.PauliString.trotterStepTraj_succ (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    trotterStepTraj Gs θ period wstar O (d + 1) =
      truncOp (highSet n wstar)ᶜ
        (traj Gs θ (trotterStepTraj Gs θ period wstar O d) period) := by sorry
