-- Prove2me | Theorems.Thm_Lean4LPD_LayerCounterexample_herm_P6_sign
-- name    : Lean4LPD.LayerCounterexample.herm_P6_sign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:36:10.024925+00:00
-- url     : https://prove2.me/theorems/aed1cb02-1445-48c2-a0da-3a7b5aa03912
-- title:
--   Layer Counterexample: herm P6 sign
-- statement:
--   The named witness `P₆` has three `Y` sites and carries the phase `3 = #{Y-sites} mod 4`,
--   whereas `herm` records only the parity of the number of `Y` sites (phase `1`). The two
--   representatives of the class differ by the phase `2`, that is by the factor `i^2 = -1`, which
--   accounts for the sign in `pf2_coeff_sines`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L539-L539
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L539-L539

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

theorem Lean4LPD.LayerCounterexample.herm_P6_sign : herm (cls P₆) = phaseMul 2 P₆ := by sorry
