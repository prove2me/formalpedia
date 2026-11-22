-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_norm_layerInflowMatrix_clm_le_restr
-- name    : Lean4LPD.PauliString.norm_layerInflowMatrix_clm_le_restr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:40.552962+00:00
-- url     : https://prove2.me/theorems/6eca407f-0c74-4c9f-96b7-b698d390d2db
-- title:
--   Pauli String: norm layer Inflow Matrix clm le restr
-- statement:
--   The `j`-jump inflow bounded by the input's norm above the lower threshold `w'`, where
--   `w' + j (k_h - 1) ≤ w`. Supporting theorem for `apd:rmk:multijump`; the coefficient is the one
--   proved in `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L983-L991
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L983-L991

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

theorem Lean4LPD.PauliString.norm_layerInflowMatrix_clm_le_restr (L : List (PauliString n × ℝ)) {kh w w' j : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (hw : w' + j * (kh - 1) ≤ w)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖Lean4LPD.clm (layerInflowMatrix L w j) y‖
      ≤ ((((w + j * (kh - 1) : ℕ) : ℝ) * σ) ^ j / (Nat.factorial j : ℝ))
        * ‖restr (highSet n w') y‖ := by sorry
