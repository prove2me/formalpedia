-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_jumpAct_apply
-- name    : Lean4LPD.PauliString.jumpAct_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:27.133631+00:00
-- url     : https://prove2.me/theorems/b86ab626-2b00-4ce2-9d8f-052029882e95
-- title:
--   Pauli String: jump Act apply
-- statement:
--   Coefficient formula for the sine branch; supporting lemma for
--   `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L112-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L112-L116

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

theorem Lean4LPD.PauliString.jumpAct_apply (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (p : PauliIndex n) :
    (jumpAct G θ y).ofLp p =
      if sympForm G (herm p) = 0 then 0
      else -(Real.sin θ : ℂ) * (partnerSign G p * y.ofLp (partner G p)) := by sorry

attribute [defeq] Lean4LPD.PauliString.jumpAct_apply
