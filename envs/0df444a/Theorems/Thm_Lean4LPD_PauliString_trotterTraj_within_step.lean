-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trotterTraj_within_step
-- name    : Lean4LPD.PauliString.trotterTraj_within_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:35:25.898027+00:00
-- url     : https://prove2.me/theorems/3eb49a9d-6039-4b8c-a416-4938de6728fa
-- title:
--   Pauli String: trotter Traj within step
-- statement:
--   Before the boundary, no truncation interrupts the block's ordinary `traj`
--   (`apd:thm:triangle`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L127-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L127-L139

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

theorem Lean4LPD.PauliString.trotterTraj_within_step (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d i : ℕ) (hi : i < period) :
    trotterTraj Gs θ period wstar O (d * period + i) =
      traj Gs θ (trotterTraj Gs θ period wstar O (d * period)) i := by sorry
