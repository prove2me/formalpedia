-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_norm_stayAct_apply_le
-- name    : Lean4LPD.PauliString.norm_stayAct_apply_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:39.464816+00:00
-- url     : https://prove2.me/theorems/b287e5d4-f7dd-48de-81e7-1b15be08fc5b
-- title:
--   Pauli String: norm stay Act apply le
-- statement:
--   The unchanged branch is a contraction in each coefficient magnitude.
--   Supporting lemma for `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L514-L521
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L514-L521

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

theorem Lean4LPD.PauliString.norm_stayAct_apply_le (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (p : PauliIndex n) :
    ‖(stayAct G θ y).ofLp p‖ ≤ ‖y.ofLp p‖ := by sorry
