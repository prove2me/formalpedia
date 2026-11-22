-- Prove2me | Theorems.Thm_Lean4LPD_LayerCounterexample_pf2Rotations_hermitian
-- name    : Lean4LPD.LayerCounterexample.pf2Rotations_hermitian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:35:56.376461+00:00
-- url     : https://prove2.me/theorems/c74a0d6d-32e4-49db-84e8-40bc42d36e70
-- title:
--   Layer Counterexample: pf2 Rotations hermitian
-- statement:
--   Every generator of the word is a Hermitian Pauli string, by `isSelfAdjoint_L₁` and
--   `isSelfAdjoint_L₂`. This is the hypothesis under which `coeffVec_layerConj` turns the matrix
--   conjugation into the coefficient action `layerAct`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L80-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L80-L88

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerCounterexample
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.LayerCounterexample
open PauliString LayerWitness Finset

theorem Lean4LPD.LayerCounterexample.pf2Rotations_hermitian (θ : ℝ) : ∀ g ∈ pf2Rotations θ, IsSelfAdjoint g.1 := by sorry
