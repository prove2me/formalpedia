-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerStepMass_reset
-- name    : Lean4LPD.PauliString.layerStepMass_reset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:02:55.717098+00:00
-- url     : https://prove2.me/theorems/a3ac6157-9bca-4aab-ad94-ed7efdf53341
-- title:
--   Pauli String: layer Step Mass reset
-- statement:
--   **Reset at the start of every step**, as required by `apd:eq:total_high_weight_norm`: the
--   mass above the cutoff vanishes at layer `0` of each step. For the first step this follows from
--   `k_o`-locality of the input and `k_o ≤ wstar`; for later steps from the preceding cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L269-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L269-L278

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

theorem Lean4LPD.PauliString.layerStepMass_reset (layers : ℕ → List (PauliString n × ℝ))
    {Γ wstar ko : ℕ} {O : Matrix (Bits n) (Bits n) ℂ}
    (hcut : ko ≤ wstar) (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (d : ℕ) :
    layerStepMass layers Γ wstar O d 0 = 0 := by sorry
