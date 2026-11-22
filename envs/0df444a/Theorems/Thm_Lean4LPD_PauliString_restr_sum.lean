-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_restr_sum
-- name    : Lean4LPD.PauliString.restr_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:15.994728+00:00
-- url     : https://prove2.me/theorems/c67921aa-0449-41bc-b834-93c85640e985
-- title:
--   Pauli String: restr sum
-- statement:
--   Finite-sum compatibility of coefficient projection. Supporting lemma for
--   `A_RB = ∑_{j≥1} A^{(j)}` in `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L898-L904
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L898-L904

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

theorem Lean4LPD.PauliString.restr_sum {ι : Type*} (s : Finset ι) (R : Finset (PauliIndex n))
    (f : ι → EuclideanSpace ℂ (PauliIndex n)) :
    restr R (∑ i ∈ s, f i) = ∑ i ∈ s, restr R (f i) := by sorry
