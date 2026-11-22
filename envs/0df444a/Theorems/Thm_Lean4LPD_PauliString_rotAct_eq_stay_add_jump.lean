-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_rotAct_eq_stay_add_jump
-- name    : Lean4LPD.PauliString.rotAct_eq_stay_add_jump
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:51.915253+00:00
-- url     : https://prove2.me/theorems/147077f0-6138-47f7-a592-1ddda8573658
-- title:
--   Pauli String: rot Act eq stay add jump
-- statement:
--   The two branches add up to the rotation action `rotAct`, which `coeffVec_conj` identifies
--   with conjugation by the rotation. Supporting lemma for `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L120-L125
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L120-L125

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

theorem Lean4LPD.PauliString.rotAct_eq_stay_add_jump (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    rotAct G θ y = stayAct G θ y + jumpAct G θ y := by sorry
