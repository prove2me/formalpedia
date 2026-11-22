-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerJump_apply_eq_sum_matrix
-- name    : Lean4LPD.PauliString.layerJump_apply_eq_sum_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:51.252433+00:00
-- url     : https://prove2.me/theorems/e13e605b-2d5a-4156-85a0-8dafbc008107
-- title:
--   Pauli String: layer Jump apply eq sum matrix
-- statement:
--   `layerJumpMatrix L j` acts on an arbitrary coefficient vector as `layerJump L j` does, not
--   only on basis vectors. Supporting lemma for `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L429-L456
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L429-L456

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

theorem Lean4LPD.PauliString.layerJump_apply_eq_sum_matrix (L : List (PauliString n × ℝ)) (j : ℕ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (p : PauliIndex n) :
    (layerJump L j y).ofLp p = ∑ q, layerJumpMatrix L j p q * y.ofLp q := by sorry
