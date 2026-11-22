-- Prove2me | Theorems.Thm_Lean4LPD_LayerCounterexample_pf2Output_eq_four_layers
-- name    : Lean4LPD.LayerCounterexample.pf2Output_eq_four_layers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:46:51.374795+00:00
-- url     : https://prove2.me/theorems/fff75082-d6b6-4a3f-8b79-55b0759084b8
-- title:
--   Layer Counterexample: pf2 Output eq four layers
-- statement:
--   The computed output is the literal four-layer `L₁,L₂,L₂,L₁` second-order formula of
--   `apd:eq:suzuki`: the nested conjugation of `Z₃` by the four layers, with the two adjacent `L₂`
--   half-steps kept separate and the same angle in every layer, not a merged or angle-rescaled
--   circuit.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L515-L520
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L515-L520

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

theorem Lean4LPD.LayerCounterexample.pf2Output_eq_four_layers (θ : ℝ) :
    pf2Output θ = layerConj (L₁.map fun G => (G, θ))
      (layerConj (L₂.map fun G => (G, θ))
        (layerConj (L₂.map fun G => (G, θ))
          (layerConj (L₁.map fun G => (G, θ)) (toMatrix (Z 3))))) := by sorry
