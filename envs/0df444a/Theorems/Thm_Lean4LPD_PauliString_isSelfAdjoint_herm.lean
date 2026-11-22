-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_herm
-- name    : Lean4LPD.PauliString.isSelfAdjoint_herm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:38.273606+00:00
-- url     : https://prove2.me/theorems/7f2f2cf0-3e5d-42be-a241-eb73c823ed1a
-- title:
--   Pauli String: is Self Adjoint herm
-- statement:
--   `herm p` is self-adjoint, so `toMatrix (herm p)` is a Hermitian operator.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L134-L135
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L134-L135

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.isSelfAdjoint_herm (p : PauliIndex n) : IsSelfAdjoint (herm p) := by sorry
