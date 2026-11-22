-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerJump_eq_zero_of_length_lt
-- name    : Lean4LPD.PauliString.layerJump_eq_zero_of_length_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:13.496397+00:00
-- url     : https://prove2.me/theorems/d6431fc9-9e57-4928-b53a-3149444e1612
-- title:
--   Pauli String: layer Jump eq zero of length lt
-- statement:
--   A layer cannot take more sine branches than it has rotations.
--   Supporting lemma for the finite form of `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L212-L224
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L212-L224

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

theorem Lean4LPD.PauliString.layerJump_eq_zero_of_length_lt (L : List (PauliString n × ℝ))
    (j : ℕ) (hj : L.length < j) (y : EuclideanSpace ℂ (PauliIndex n)) :
    layerJump L j y = 0 := by sorry
