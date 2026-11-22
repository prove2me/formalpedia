-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trotterTraj_next_boundary
-- name    : Lean4LPD.PauliString.trotterTraj_next_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:16.363914+00:00
-- url     : https://prove2.me/theorems/de6b7a66-eb94-4131-ab13-1ea3fd324e0e
-- title:
--   Pauli String: trotter Traj next boundary
-- statement:
--   Over one complete block, the scheduled trajectory evolves without truncation and is then
--   cut (`apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L143-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L143-L158

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

theorem Lean4LPD.PauliString.trotterTraj_next_boundary (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hp : 0 < period) :
    trotterTraj Gs θ period wstar O ((d + 1) * period) =
      truncOp (highSet n wstar)ᶜ
        (traj Gs θ (trotterTraj Gs θ period wstar O (d * period)) period) := by sorry
