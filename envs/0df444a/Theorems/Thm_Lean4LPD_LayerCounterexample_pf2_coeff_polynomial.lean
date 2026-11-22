-- Prove2me | Theorems.Thm_Lean4LPD_LayerCounterexample_pf2_coeff_polynomial
-- name    : Lean4LPD.LayerCounterexample.pf2_coeff_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:36:00.736155+00:00
-- url     : https://prove2.me/theorems/b91d10c7-808a-441f-add4-9b56fc71c751
-- title:
--   Layer Counterexample: pf2 coeff polynomial
-- statement:
--   **The coefficient of `P₆` as a polynomial in `cos θ` and `sin θ`.** The coefficient of
--   `pf2Output θ` at the weight-six class `cls P₆` equals `-4 (cos θ)^2 (sin θ)^5`, obtained by
--   unfolding the coefficient recurrence `rotAct_apply` through the fourteen rotations of the literal
--   second-order word. The sign refers to the canonical representative `herm (cls P₆)`; see
--   `pf2_named_P6_component` for the component on `P₆` itself.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L489-L497
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L489-L497

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

theorem Lean4LPD.LayerCounterexample.pf2_coeff_polynomial (θ : ℝ) :
    coeff (pf2Output θ) (cls P₆) =
      -4 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 5 := by sorry
