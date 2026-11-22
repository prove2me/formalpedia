-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trotterSchedule_boundary
-- name    : Lean4LPD.PauliString.trotterSchedule_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:36:28.641277+00:00
-- url     : https://prove2.me/theorems/d828a939-e379-42f9-ba60-2f976ed20e04
-- title:
--   Pauli String: trotter Schedule boundary
-- statement:
--   The last rotation of each nonempty block is followed by the weight cut
--   (`apd:thm:triangle`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L72-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L72-L77

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

theorem Lean4LPD.PauliString.trotterSchedule_boundary (period wstar d : ℕ) (hp : 0 < period) :
    trotterSchedule (n := n) period wstar (d * period + (period - 1)) =
      (highSet n wstar)ᶜ := by sorry
