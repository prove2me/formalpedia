-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_layerBlockEnd_pow
-- name    : Lean4LPD.PauliString.pauliNorm_layerBlockEnd_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:33.316192+00:00
-- url     : https://prove2.me/theorems/79321ad0-e719-492d-b540-486b2663c12b
-- title:
--   Pauli String: pauli Norm layer Block End pow
-- statement:
--   Every power of the block evolution preserves the normalized Pauli norm, for Hermitian
--   generators (`apd:thm:triangle`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L438-L446
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L438-L446

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

theorem Lean4LPD.PauliString.pauliNorm_layerBlockEnd_pow (layers : ℕ → List (PauliString n × ℝ))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O) = pauliNorm O := by sorry
