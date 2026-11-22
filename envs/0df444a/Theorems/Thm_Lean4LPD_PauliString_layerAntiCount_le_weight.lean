-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerAntiCount_le_weight
-- name    : Lean4LPD.PauliString.layerAntiCount_le_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:26.674452+00:00
-- url     : https://prove2.me/theorems/9e5da7ef-988c-46a3-b60b-1cb20c4b5332
-- title:
--   Pauli String: layer Anti Count le weight
-- statement:
--   The anticommuting-rotation list count is bounded by Pauli weight for a disjoint layer.
--   Supporting lemma for `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L578-L581
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L578-L581

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

theorem Lean4LPD.PauliString.layerAntiCount_le_weight (L : List (PauliString n)) {kh : ℕ}
    (hL : IsLayer kh L) (p : PauliIndex n) : layerAntiCount L p ≤ wt p := by sorry
