-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_coeffVec_layerConj
-- name    : Lean4LPD.PauliString.coeffVec_layerConj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:22.120437+00:00
-- url     : https://prove2.me/theorems/3474fa5a-5032-42cd-b92b-b843fb288a56
-- title:
--   Pauli String: coeff Vec layer Conj
-- statement:
--   For Hermitian generators, `layerAct L` is the action of the matrix conjugation `layerConj L`
--   on coefficient vectors. Supporting lemma for `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L175-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L175-L183

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

theorem Lean4LPD.PauliString.coeffVec_layerConj (L : List (PauliString n × ℝ))
    (hL : ∀ g ∈ L, IsSelfAdjoint g.1) (O : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (layerConj L O) = layerAct L (coeffVec O) := by sorry
