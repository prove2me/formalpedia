-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_card_antiLayer_powersetCard_le
-- name    : Lean4LPD.PauliString.card_antiLayer_powersetCard_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:37.451131+00:00
-- url     : https://prove2.me/theorems/4ec7f052-5736-45f1-8f27-1561db12e280
-- title:
--   Pauli String: card anti Layer powerset Card le
-- statement:
--   The number of `j`-element subsets of `𝒜(p)` is at most `C(|p|, j)`. This is the
--   subset-counting part of the row and column estimates in `apd:thm:layer_inflow`. The matrix
--   entries themselves are bounded in `row_sum_norm_layerJumpMatrix_le` and
--   `col_sum_norm_layerJumpMatrix_le`, through `layerAntiCount`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L368-L372
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L368-L372

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

theorem Lean4LPD.PauliString.card_antiLayer_powersetCard_le (L : List (PauliString n)) {kh : ℕ}
    (hL : IsLayer kh L) (p : PauliIndex n) (j : ℕ) :
    ((antiLayer L p).powersetCard j).card ≤ (wt p).choose j := by sorry
