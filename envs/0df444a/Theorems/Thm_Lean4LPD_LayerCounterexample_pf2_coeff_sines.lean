-- Prove2me | Theorems.Thm_Lean4LPD_LayerCounterexample_pf2_coeff_sines
-- name    : Lean4LPD.LayerCounterexample.pf2_coeff_sines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:35:54.096638+00:00
-- url     : https://prove2.me/theorems/20a03c99-88ea-44cd-b3ec-f8cb421edc8f
-- title:
--   Layer Counterexample: pf2 coeff sines
-- statement:
--   **The coefficient in product form, `-(sin θ)^3 (sin 2θ)^2`.** This is
--   `pf2_coeff_polynomial` rewritten with `sin 2θ = 2 sin θ cos θ`; in this form it is evident that
--   the coefficient is nonzero at every small angle (`pf2_coeff_ne_zero`). The minus sign is that of
--   the canonical representative `herm (cls P₆)`, not of the tensor product `P₆` itself
--   (`herm_P6_sign`). This upgrades the reachability witness `LayerWitness.P₆_mem_reachable_unmerged`
--   to an actual coefficient.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L528-L533
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L528-L533

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

theorem Lean4LPD.LayerCounterexample.pf2_coeff_sines (θ : ℝ) :
    coeff (pf2Output θ) (cls P₆) =
      -(Real.sin θ : ℂ) ^ 3 * (Real.sin (2 * θ) : ℂ) ^ 2 := by sorry
