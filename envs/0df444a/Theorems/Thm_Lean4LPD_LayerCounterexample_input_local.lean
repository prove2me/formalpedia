-- Prove2me | Theorems.Thm_Lean4LPD_LayerCounterexample_input_local
-- name    : Lean4LPD.LayerCounterexample.input_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:47:01.067626+00:00
-- url     : https://prove2.me/theorems/902136fd-3228-499a-a5bb-65b1229c4bb1
-- title:
--   Layer Counterexample: input local
-- statement:
--   The input `Z₃` satisfies the weight-one cutoff: its coefficients at all classes of weight
--   greater than `1` vanish. So the step starts from an operator of weight at most `w* = 1`, as the
--   truncated input in `apd:eq:step_component` does, rather than from a large initial observable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L554-L557
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L554-L557

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

theorem Lean4LPD.LayerCounterexample.input_local : ∀ p : PauliIndex 8, 1 < wt p → coeff (toMatrix (Z 3)) p = 0 := by sorry
