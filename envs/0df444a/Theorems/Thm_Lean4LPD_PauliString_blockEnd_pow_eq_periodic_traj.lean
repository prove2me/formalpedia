-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_blockEnd_pow_eq_periodic_traj
-- name    : Lean4LPD.PauliString.blockEnd_pow_eq_periodic_traj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:41:58.895929+00:00
-- url     : https://prove2.me/theorems/a16d8f8d-1f03-4b83-80c1-1554aa270dcd
-- title:
--   Pauli String: block End pow eq periodic traj
-- statement:
--   The `r`-th power of the block evolution is the rotation-indexed untruncated `traj` at
--   `r * period`, with the rotations repeated modulo `period`. This identifies the untruncated
--   operator in `apd:thm:triangle`. It holds for every block length, including the empty block.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L179-L188
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L179-L188

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

theorem Lean4LPD.PauliString.blockEnd_pow_eq_periodic_traj (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    ((blockEnd Gs θ period) ^ r) O =
      traj (fun g => Gs (g % period)) (fun g => θ (g % period)) O (r * period) := by sorry
