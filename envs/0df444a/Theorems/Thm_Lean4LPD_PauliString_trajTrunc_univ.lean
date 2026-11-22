-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trajTrunc_univ
-- name    : Lean4LPD.PauliString.trajTrunc_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:39.010357+00:00
-- url     : https://prove2.me/theorems/5b98921f-1ae2-41a8-a1c3-48abbbcb0e44
-- title:
--   Pauli String: traj Trunc univ
-- statement:
--   **Truncating nothing is `traj`.** The guard that `trajTrunc` generalizes `Flow.lean`'s
--   trajectory rather than replacing it with an incomparable object; it is an equality of *operators*,
--   which is what `truncOp_univ` buys.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Truncate.lean#L244-L248
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Truncate.lean#L244-L248

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

theorem Lean4LPD.PauliString.trajTrunc_univ (Gs : ℕ → PauliString n) (θ : ℕ → ℝ) (O : Matrix (Bits n) (Bits n) ℂ)
    (g : ℕ) : trajTrunc Gs θ (fun _ => univ) O g = traj Gs θ O g := by sorry
