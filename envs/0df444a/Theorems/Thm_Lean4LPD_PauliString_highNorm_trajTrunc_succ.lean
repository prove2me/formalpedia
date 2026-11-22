-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_highNorm_trajTrunc_succ
-- name    : Lean4LPD.PauliString.highNorm_trajTrunc_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:48.441926+00:00
-- url     : https://prove2.me/theorems/ecf9643e-8158-4ec3-bf94-d9328131edcf
-- title:
--   Pauli String: high Norm traj Trunc succ
-- statement:
--   **The per-rotation-cut state carries no weight above `w*`.** A support fact, **not** a
--   non-vacuity witness: its conclusion follows from `highNorm_truncOp_compl`.
--   The algorithm's boundary-scheduled version is `highNorm_trotterStepTraj_succ` in
--   `Pauli/TrotterTruncate.lean` (`apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Truncate.lean#L267-L271
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Truncate.lean#L267-L271

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n ko kh : ℕ}

theorem Lean4LPD.PauliString.highNorm_trajTrunc_succ (wstar : ℕ) (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    highNorm wstar (trajTrunc Gs θ (fun _ => (highSet n wstar)ᶜ) O (g + 1)) = 0 := by sorry
