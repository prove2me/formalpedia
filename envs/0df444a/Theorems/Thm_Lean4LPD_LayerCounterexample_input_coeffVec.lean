-- Prove2me | Theorems.Thm_Lean4LPD_LayerCounterexample_input_coeffVec
-- name    : Lean4LPD.LayerCounterexample.input_coeffVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:07.5448+00:00
-- url     : https://prove2.me/theorems/41a17d13-b6aa-4bc2-99a0-d3e3fd6a5757
-- title:
--   Layer Counterexample: input coeff Vec
-- statement:
--   The coefficient vector of the input `Z₃` is the unit vector at its class `cls (Z 3)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L95-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L95-L99

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerCounterexample
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.LayerCounterexample
open PauliString LayerWitness Finset

theorem Lean4LPD.LayerCounterexample.input_coeffVec : coeffVec (toMatrix (Z (3 : Fin 8))) =
    WithLp.toLp 2 (Pi.single (cls (Z (3 : Fin 8))) (1 : ℂ)) := by sorry
