-- Prove2me | Theorems.Thm_Lean4LPD_LayerCounterexample_pf2Discard_coeff
-- name    : Lean4LPD.LayerCounterexample.pf2Discard_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:33.066174+00:00
-- url     : https://prove2.me/theorems/f8d181c4-6672-42a6-896a-6fae3ac83bc9
-- title:
--   Layer Counterexample: pf2 Discard coeff
-- statement:
--   The weight-six coefficient is preserved in the discarded operator: `pf2Discard θ` and
--   `pf2Output θ` have the same coefficient at `cls P₆`, because `wt (cls P₆) = 6 > 1` puts that
--   class outside the retained set. This is the truncation step that a reachability argument alone
--   does not provide.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L580-L583
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L580-L583

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

theorem Lean4LPD.LayerCounterexample.pf2Discard_coeff (θ : ℝ) :
    coeff (pf2Discard θ) (cls P₆) = coeff (pf2Output θ) (cls P₆) := by sorry
