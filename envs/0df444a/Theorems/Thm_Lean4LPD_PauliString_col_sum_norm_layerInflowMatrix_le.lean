-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_col_sum_norm_layerInflowMatrix_le
-- name    : Lean4LPD.PauliString.col_sum_norm_layerInflowMatrix_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:08.30368+00:00
-- url     : https://prove2.me/theorems/88f72a62-e215-4e0e-a9dc-19db85b9551c
-- title:
--   Pauli String: col sum norm layer Inflow Matrix le
-- statement:
--   **Column bound for the high-from-low exactly-`j` block.**
--   Formalizes the column estimate of `apd:thm:layer_inflow`: a nonzero column has weight at most
--   `w`. The angles are unrestricted and enter only through the bound `σ` on their absolute sines.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L790-L810
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L790-L810

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

theorem Lean4LPD.PauliString.col_sum_norm_layerInflowMatrix_le (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (w j : ℕ) (q : PauliIndex n) :
    ∑ p, ‖layerInflowMatrix L w j p q‖ ≤ (w.choose j : ℝ) * σ ^ j := by sorry
