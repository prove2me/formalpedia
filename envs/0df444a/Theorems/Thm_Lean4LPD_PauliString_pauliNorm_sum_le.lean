-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sum_le
-- name    : Lean4LPD.PauliString.pauliNorm_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:41:32.828594+00:00
-- url     : https://prove2.me/theorems/b16526bb-683a-4606-bb74-85560ff49dec
-- title:
--   Pauli String: pauli Norm sum le
-- statement:
--   Finite-sum Minkowski for the normalized Pauli norm, the norm-level triangle step associated
--   with the operator telescope in `apd:thm:triangle`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L88-L96
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L88-L96

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

theorem Lean4LPD.PauliString.pauliNorm_sum_le {ι : Type*} (S : Finset ι)
    (A : ι → Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (∑ i ∈ S, A i) ≤ ∑ i ∈ S, pauliNorm (A i) := by sorry
