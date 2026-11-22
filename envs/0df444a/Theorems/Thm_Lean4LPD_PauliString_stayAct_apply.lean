-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_stayAct_apply
-- name    : Lean4LPD.PauliString.stayAct_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:11.98989+00:00
-- url     : https://prove2.me/theorems/dd2012f7-0b09-4522-a7f5-b93f5ed13157
-- title:
--   Pauli String: stay Act apply
-- statement:
--   Coefficient formula for the unchanged branch; supporting lemma for
--   `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L105-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L105-L108

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

theorem Lean4LPD.PauliString.stayAct_apply (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (p : PauliIndex n) :
    (stayAct G θ y).ofLp p =
      if sympForm G (herm p) = 0 then y.ofLp p else (Real.cos θ : ℂ) * y.ofLp p := by sorry

attribute [defeq] Lean4LPD.PauliString.stayAct_apply
