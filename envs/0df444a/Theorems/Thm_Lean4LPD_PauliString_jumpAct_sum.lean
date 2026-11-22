-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_jumpAct_sum
-- name    : Lean4LPD.PauliString.jumpAct_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:15.372967+00:00
-- url     : https://prove2.me/theorems/f4c41b66-35bf-4d10-a03d-c70558baa4db
-- title:
--   Pauli String: jump Act sum
-- statement:
--   The sine branch distributes over finite coefficient sums; supporting lemma for
--   `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L238-L244
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L238-L244

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

theorem Lean4LPD.PauliString.jumpAct_sum {ι : Type*} (s : Finset ι) (G : PauliString n) (θ : ℝ)
    (f : ι → EuclideanSpace ℂ (PauliIndex n)) :
    jumpAct G θ (∑ i ∈ s, f i) = ∑ i ∈ s, jumpAct G θ (f i) := by sorry
