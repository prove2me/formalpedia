-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sum_norm_jumpAct_le
-- name    : Lean4LPD.PauliString.sum_norm_jumpAct_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:00.52912+00:00
-- url     : https://prove2.me/theorems/da6721e7-72e8-4eed-a23c-97486a455c45
-- title:
--   Pauli String: sum norm jump Act le
-- statement:
--   The sine branch contracts the coefficient `ℓ¹` norm by its absolute sine. Supporting
--   lemma for the column estimate of `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L545-L554
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L545-L554

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

theorem Lean4LPD.PauliString.sum_norm_jumpAct_le (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ∑ p, ‖(jumpAct G θ y).ofLp p‖ ≤ |Real.sin θ| * ∑ p, ‖y.ofLp p‖ := by sorry
