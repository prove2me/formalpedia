-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_generators_weight
-- name    : Lean4LPD.DiscardWitness.generators_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:56.86895+00:00
-- url     : https://prove2.me/theorems/edf184d6-2e10-4070-b354-d2b21cbe6238
-- title:
--   Discard Witness: generators weight
-- statement:
--   Concrete regression data for `apd:eq:step_component`: every generator has exactly
--   `k_h = 2`, rather than only a degenerate upper bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L196-L200
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L196-L200

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.generators_weight (g : ℕ) : weight (Gs g) = 2 := by sorry
