-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_row_sum_norm_layerInflowMatrix_le
-- name    : Lean4LPD.PauliString.row_sum_norm_layerInflowMatrix_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:57.833449+00:00
-- url     : https://prove2.me/theorems/03da76a9-031e-4536-8277-282b126e59f6
-- title:
--   Pauli String: row sum norm layer Inflow Matrix le
-- statement:
--   **Row bound for the high-from-low exactly-`j` block.**
--   Formalizes the row estimate of `apd:thm:layer_inflow`: a nonzero row has weight at most
--   `w + j (k_h - 1)` by `layerJump_single_eq_zero_of_weight_lt`, and in a disjoint-support layer at
--   most that many generators anticommute with it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L755-L785
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L755-L785

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

theorem Lean4LPD.PauliString.row_sum_norm_layerInflowMatrix_le (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (w j : ℕ) (p : PauliIndex n) :
    ∑ q, ‖layerInflowMatrix L w j p q‖
      ≤ ((w + j * (kh - 1)).choose j : ℝ) * σ ^ j := by sorry
