-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_highNorm_truncOp_compl
-- name    : Lean4LPD.PauliString.highNorm_truncOp_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:42.483798+00:00
-- url     : https://prove2.me/theorems/b0bc1945-0e60-4a0b-a82f-3920c3864350
-- title:
--   Pauli String: high Norm trunc Op compl
-- statement:
--   **`Π_{≤ w}` leaves nothing above `w`.** The defining property of the algorithm's state: after
--   truncating at threshold `w`, the high-weight mass is exactly zero, not merely smaller. Without
--   this, `trajTrunc` would be a flow with *some* mass removed rather than the LPD one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Truncate.lean#L208-L211
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Truncate.lean#L208-L211

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

theorem Lean4LPD.PauliString.highNorm_truncOp_compl (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm w (truncOp (highSet n w)ᶜ O) = 0 := by sorry
