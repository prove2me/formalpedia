-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_layerBlockTraj
-- name    : Lean4LPD.PauliString.pauliNorm_layerBlockTraj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:45.891352+00:00
-- url     : https://prove2.me/theorems/925b2f1c-0cb1-4986-86bf-5d258cb53486
-- title:
--   Pauli String: pauli Norm layer Block Traj
-- statement:
--   A whole Hermitian layer block preserves the normalized Pauli norm, supporting the
--   norm-level triangle counterpart of `apd:thm:triangle`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L428-L434
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L428-L434

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}

theorem Lean4LPD.PauliString.pauliNorm_layerBlockTraj (layers : ℕ → List (PauliString n × ℝ))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1)
    (O : Matrix (Bits n) (Bits n) ℂ) (i : ℕ) :
    pauliNorm (layerBlockTraj layers O i) = pauliNorm O := by sorry
