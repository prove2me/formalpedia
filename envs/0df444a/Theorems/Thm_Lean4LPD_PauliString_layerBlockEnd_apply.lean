-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerBlockEnd_apply
-- name    : Lean4LPD.PauliString.layerBlockEnd_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:02:31.499212+00:00
-- url     : https://prove2.me/theorems/728ff2b6-cfa4-4d27-9b12-a613433e7baa
-- title:
--   Pauli String: layer Block End apply
-- statement:
--   `layerBlockEnd` applies the matrix evolution `layerBlockTraj` through `Γ` layers
--   (`apd:thm:triangle`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L397-L398
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L397-L398

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

theorem Lean4LPD.PauliString.layerBlockEnd_apply (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (A : Matrix (Bits n) (Bits n) ℂ) : layerBlockEnd layers Γ A = layerBlockTraj layers A Γ := by sorry

attribute [defeq] Lean4LPD.PauliString.layerBlockEnd_apply
