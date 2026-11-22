-- Prove2me | Theorems.Thm_Lean4LPD_LayerCounterexample_pf2_named_P6_component
-- name    : Lean4LPD.LayerCounterexample.pf2_named_P6_component
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:47:15.189571+00:00
-- url     : https://prove2.me/theorems/cf0aa82a-1a35-4f67-9018-e7c3006d21fc
-- title:
--   Layer Counterexample: pf2 named P6 component
-- statement:
--   On the **named positive tensor `P₆`**, the amplitude is `sin³θ sin²(2θ)`.
--   This is an operator-component identity, with `coeff • toMatrix (herm (cls P₆))` on the left, not
--   an identification of classes up to an unspecified phase.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L544-L549
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L544-L549

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerCounterexample
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.LayerCounterexample
open PauliString LayerWitness Finset
attribute [local irreducible] layerAct

theorem Lean4LPD.LayerCounterexample.pf2_named_P6_component (θ : ℝ) :
    coeff (pf2Output θ) (cls P₆) • toMatrix (herm (cls P₆)) =
      ((Real.sin θ : ℂ) ^ 3 * (Real.sin (2 * θ) : ℂ) ^ 2) • toMatrix P₆ := by sorry
