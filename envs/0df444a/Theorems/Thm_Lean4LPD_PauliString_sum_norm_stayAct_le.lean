-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sum_norm_stayAct_le
-- name    : Lean4LPD.PauliString.sum_norm_stayAct_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:50.960537+00:00
-- url     : https://prove2.me/theorems/56480333-c336-43fb-8f77-ac3a3a602992
-- title:
--   Pauli String: sum norm stay Act le
-- statement:
--   The unchanged branch contracts the coefficient `ℓ¹` norm. Supporting lemma for the
--   column estimate of `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L538-L541
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L538-L541

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

theorem Lean4LPD.PauliString.sum_norm_stayAct_le (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ∑ p, ‖(stayAct G θ y).ofLp p‖ ≤ ∑ p, ‖y.ofLp p‖ := by sorry
