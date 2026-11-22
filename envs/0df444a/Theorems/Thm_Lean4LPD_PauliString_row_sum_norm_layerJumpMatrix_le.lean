-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_row_sum_norm_layerJumpMatrix_le
-- name    : Lean4LPD.PauliString.row_sum_norm_layerJumpMatrix_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:53.505873+00:00
-- url     : https://prove2.me/theorems/c0c0c524-c11f-4f6b-b172-60c835dd7877
-- title:
--   Pauli String: row sum norm layer Jump Matrix le
-- statement:
--   **Absolute row sums of the exactly-`j` matrix.** Row `p` of `layerJumpMatrix L j` has
--   absolute sum at most `C(c, j) σ^j`, where `c` is the number of rotations of the layer that
--   anticommute with `p`. Supporting theorem for the Schur step in `apd:thm:layer_inflow`.
--   Pairwise commutation suffices for this estimate; disjoint supports are used afterwards, to bound
--   `layerAntiCount` by the Pauli weight of `p`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L588-L647
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L588-L647

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

theorem Lean4LPD.PauliString.row_sum_norm_layerJumpMatrix_le (L : List (PauliString n × ℝ))
    (hcomm : ∀ g ∈ L, ∀ h ∈ L, sympForm g.1 h.1 = 0)
    {σ : ℝ} (hσ : 0 ≤ σ) (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ)
    (j : ℕ) (p : PauliIndex n) :
    ∑ q, ‖layerJumpMatrix L j p q‖
      ≤ ((layerAntiCount (L.map Prod.fst) p).choose j : ℝ) * σ ^ j := by sorry
