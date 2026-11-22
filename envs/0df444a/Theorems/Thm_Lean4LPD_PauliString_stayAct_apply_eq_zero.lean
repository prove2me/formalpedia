-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_stayAct_apply_eq_zero
-- name    : Lean4LPD.PauliString.stayAct_apply_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:48.363375+00:00
-- url     : https://prove2.me/theorems/f5d5a229-9142-4556-8e7c-d46ea2d8c8b8
-- title:
--   Pauli String: stay Act apply eq zero
-- statement:
--   A zero input coordinate stays zero in the unchanged branch; supporting lemma for
--   `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L271-L274
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L271-L274

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

theorem Lean4LPD.PauliString.stayAct_apply_eq_zero (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (p : PauliIndex n) (hy : y.ofLp p = 0) :
    (stayAct G θ y).ofLp p = 0 := by sorry
