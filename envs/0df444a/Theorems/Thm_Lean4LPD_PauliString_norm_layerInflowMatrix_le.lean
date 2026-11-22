-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_norm_layerInflowMatrix_le
-- name    : Lean4LPD.PauliString.norm_layerInflowMatrix_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:25.776361+00:00
-- url     : https://prove2.me/theorems/489ae40b-9f76-4195-8bb8-b41ac48c8250
-- title:
--   Pauli String: norm layer Inflow Matrix le
-- statement:
--   **Layer inflow, binomial form.** Formalizes the first inequality of `apd:eq:layer_inflow` in
--   `apd:thm:layer_inflow`, for any `σ` dominating every absolute sine and an arbitrary threshold
--   `w`. The Schur test combines the row bound with the (smaller) column bound. The matrix is built
--   from the rotations themselves, so no flow inequality is assumed.
--   At `w = w_m`, the upper weight is `w_m + j (k_h - 1) = w_{m+j}` for `m ≥ 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L817-L827
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L817-L827

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

theorem Lean4LPD.PauliString.norm_layerInflowMatrix_le (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (w j : ℕ) :
    ‖layerInflowMatrix L w j‖ ≤ ((w + j * (kh - 1)).choose j : ℝ) * σ ^ j := by sorry
