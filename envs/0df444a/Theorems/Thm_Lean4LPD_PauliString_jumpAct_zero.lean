-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_jumpAct_zero
-- name    : Lean4LPD.PauliString.jumpAct_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:32.221862+00:00
-- url     : https://prove2.me/theorems/957fbad4-3fa3-43f7-8cc8-20476d7d6101
-- title:
--   Pauli String: jump Act zero
-- statement:
--   Zero is preserved by the sine branch; supporting lemma for
--   `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L153-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L153-L155

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

theorem Lean4LPD.PauliString.jumpAct_zero (G : PauliString n) (θ : ℝ) : jumpAct G θ 0 = 0 := by sorry
