-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_discardedLayerStep
-- name    : Lean4LPD.PauliString.pauliNorm_discardedLayerStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:02:51.142504+00:00
-- url     : https://prove2.me/theorems/2df65190-621f-4b6e-8d34-e4d9038530b0
-- title:
--   Pauli String: pauli Norm discarded Layer Step
-- statement:
--   The Pauli norm of the discarded operator is the high-weight norm of the operator **before**
--   the cut (`apd:thm:triangle`; `apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L245-L249
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L245-L249

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

theorem Lean4LPD.PauliString.pauliNorm_discardedLayerStep (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    pauliNorm (discardedLayerStep layers Γ wstar O d) =
      highNorm wstar (layerBlockTraj layers (layerStepTraj layers Γ wstar O d) Γ) := by sorry
