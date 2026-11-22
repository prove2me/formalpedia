-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_col_sum_norm_layerJumpMatrix_le
-- name    : Lean4LPD.PauliString.col_sum_norm_layerJumpMatrix_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:09.214391+00:00
-- url     : https://prove2.me/theorems/c0ad3ada-56ec-498c-94dc-9f42bd80d8a3
-- title:
--   Pauli String: col sum norm layer Jump Matrix le
-- statement:
--   **Absolute column sums of the exactly-`j` matrix.** Column `q` of `layerJumpMatrix L j` has
--   absolute sum at most `C(c, j) σ^j`, where `c` is the number of rotations of the layer that
--   anticommute with `q`. Supporting theorem for the Schur step in `apd:thm:layer_inflow`.
--   The proof uses preservation of the commutation class (`jumpAct_layerJump_single_eq_zero`) and
--   Pascal's rule; it does not assume that distinct choices of branches give distinct nonzero
--   entries.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L674-L731
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L674-L731

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

theorem Lean4LPD.PauliString.col_sum_norm_layerJumpMatrix_le (L : List (PauliString n × ℝ))
    (hcomm : ∀ g ∈ L, ∀ h ∈ L, sympForm g.1 h.1 = 0)
    {σ : ℝ} (hσ : 0 ≤ σ) (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ)
    (j : ℕ) (q : PauliIndex n) :
    ∑ p, ‖layerJumpMatrix L j p q‖
      ≤ ((layerAntiCount (L.map Prod.fst) q).choose j : ℝ) * σ ^ j := by sorry
