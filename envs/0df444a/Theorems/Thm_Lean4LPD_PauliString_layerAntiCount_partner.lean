-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerAntiCount_partner
-- name    : Lean4LPD.PauliString.layerAntiCount_partner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:46.075216+00:00
-- url     : https://prove2.me/theorems/9ec88acf-c4b3-4299-b1fe-e2ee865b80a3
-- title:
--   Pauli String: layer Anti Count partner
-- statement:
--   Partner translation in a commuting layer preserves its anticommuting-rotation count.
--   Supporting lemma for `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L466-L475
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L466-L475

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

theorem Lean4LPD.PauliString.layerAntiCount_partner (L : List (PauliString n)) (G : PauliString n)
    (hG : ∀ H ∈ L, sympForm H G = 0) (p : PauliIndex n) :
    layerAntiCount L (partner G p) = layerAntiCount L p := by sorry
