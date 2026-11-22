-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trotterSchedule_interior
-- name    : Lean4LPD.PauliString.trotterSchedule_interior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:36:32.533751+00:00
-- url     : https://prove2.me/theorems/558a0d16-76dc-4bcb-b470-12b53e80dcc7
-- title:
--   Pauli String: trotter Schedule interior
-- statement:
--   No cutoff inside a block, as required by `apd:thm:triangle`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L63-L68
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L63-L68

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

theorem Lean4LPD.PauliString.trotterSchedule_interior (period wstar d i : ℕ) (hi : i + 1 < period) :
    trotterSchedule (n := n) period wstar (d * period + i) = univ := by sorry
