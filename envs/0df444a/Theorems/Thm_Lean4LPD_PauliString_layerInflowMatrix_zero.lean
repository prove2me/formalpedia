-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerInflowMatrix_zero
-- name    : Lean4LPD.PauliString.layerInflowMatrix_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:53.212159+00:00
-- url     : https://prove2.me/theorems/54c88ca9-22de-4a9f-aad8-9ddb8e4ac45c
-- title:
--   Pauli String: layer Inflow Matrix zero
-- statement:
--   The zero-sine branch is diagonal, so its high-from-low block vanishes.
--   Supporting lemma for `A_RB = ∑_{j≥1} A^{(j)}` in `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L873-L882
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L873-L882

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

theorem Lean4LPD.PauliString.layerInflowMatrix_zero (L : List (PauliString n × ℝ)) (w : ℕ) :
    layerInflowMatrix L w 0 = 0 := by sorry
