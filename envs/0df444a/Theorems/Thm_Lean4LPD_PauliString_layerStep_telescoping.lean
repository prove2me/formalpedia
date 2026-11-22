-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerStep_telescoping
-- name    : Lean4LPD.PauliString.layerStep_telescoping
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:05.765806+00:00
-- url     : https://prove2.me/theorems/6a5bb84b-0efd-4521-b4f7-27e0b7762838
-- title:
--   Pauli String: layer Step telescoping
-- statement:
--   **The operator telescope for layered steps.** This is the identity in `apd:thm:triangle`:
--   the untruncated evolution minus the LPD output after `r` steps is the sum of the discarded
--   operators `discardedLayerStep`, each evolved through the remaining whole blocks.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L403-L424
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L403-L424

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

theorem Lean4LPD.PauliString.layerStep_telescoping (layers : ℕ → List (PauliString n × ℝ)) (Γ wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    ((layerBlockEnd layers Γ) ^ r) O - layerStepTraj layers Γ wstar O r =
      ∑ d ∈ range r, ((layerBlockEnd layers Γ) ^ (r - 1 - d))
        (discardedLayerStep layers Γ wstar O d) := by sorry
