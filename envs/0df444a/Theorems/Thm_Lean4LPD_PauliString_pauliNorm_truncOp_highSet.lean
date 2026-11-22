-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_truncOp_highSet
-- name    : Lean4LPD.PauliString.pauliNorm_truncOp_highSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:56.304796+00:00
-- url     : https://prove2.me/theorems/b9af8735-92bb-4eba-851a-1b7057bb4dc5
-- title:
--   Pauli String: pauli Norm trunc Op high Set
-- statement:
--   The high-weight projection has norm `highNorm`, identifying the high-weight operator norm
--   appearing in `apd:thm:triangle`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L122-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L122-L124

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.pauliNorm_truncOp_highSet (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (truncOp (highSet n w) O) = highNorm w O := by sorry
