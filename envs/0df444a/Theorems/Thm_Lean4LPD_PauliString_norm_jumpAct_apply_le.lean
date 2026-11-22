-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_norm_jumpAct_apply_le
-- name    : Lean4LPD.PauliString.norm_jumpAct_apply_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:24.45647+00:00
-- url     : https://prove2.me/theorems/76282fb7-de20-4848-9112-c306aafc99ca
-- title:
--   Pauli String: norm jump Act apply le
-- statement:
--   The sine-branch coefficient is bounded by the absolute sine times its partner coefficient.
--   Supporting lemma for `apd:thm:layer_inflow`. No Hermitian hypothesis is needed
--   for this magnitude statement: `partnerSign` is always a fourth root of unity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L526-L534
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L526-L534

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

theorem Lean4LPD.PauliString.norm_jumpAct_apply_le (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (p : PauliIndex n) :
    ‖(jumpAct G θ y).ofLp p‖ ≤ |Real.sin θ| * ‖y.ofLp (partner G p)‖ := by sorry
