-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_layerStep_error_le
-- name    : Lean4LPD.PauliString.pauliNorm_layerStep_error_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:29.294795+00:00
-- url     : https://prove2.me/theorems/4d5b0bf7-d9c6-41f5-ad26-c0f59b1062b0
-- title:
--   Pauli String: pauli Norm layer Step error le
-- statement:
--   **The truncation error is at most the sum of the discarded Pauli norms.**
--   This is the norm-level part of `apd:thm:triangle`, in the normalized Pauli 2-norm. It is neither
--   a bound on expectation values nor a bound in the matrix operator norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L451-L458
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L451-L458

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

theorem Lean4LPD.PauliString.pauliNorm_layerStep_error_le (layers : ℕ → List (PauliString n × ℝ))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) (Γ wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O - layerStepTraj layers Γ wstar O r) ≤
      ∑ d ∈ range r, pauliNorm (discardedLayerStep layers Γ wstar O d) := by sorry
