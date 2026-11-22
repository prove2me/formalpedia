-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_blockEnd_apply
-- name    : Lean4LPD.PauliString.blockEnd_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:07.662805+00:00
-- url     : https://prove2.me/theorems/86848852-8266-4117-93a4-e37d351f2958
-- title:
--   Pauli String: block End apply
-- statement:
--   `blockEnd` applies the untruncated `traj` through one block, the evolution that appears in
--   `apd:eq:step_component`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L125-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L125-L127

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

theorem Lean4LPD.PauliString.blockEnd_apply (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period : ℕ) (A : Matrix (Bits n) (Bits n) ℂ) :
    blockEnd Gs θ period A = traj Gs θ A period := by sorry

attribute [defeq] Lean4LPD.PauliString.blockEnd_apply
