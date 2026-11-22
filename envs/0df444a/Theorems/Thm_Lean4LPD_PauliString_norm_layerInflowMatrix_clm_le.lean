-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_norm_layerInflowMatrix_clm_le
-- name    : Lean4LPD.PauliString.norm_layerInflowMatrix_clm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:35.434956+00:00
-- url     : https://prove2.me/theorems/ee32e8f7-6766-43bc-b565-0f7831b51051
-- title:
--   Pauli String: norm layer Inflow Matrix clm le
-- statement:
--   The `j`-jump inflow of a coefficient vector is bounded by the factorial inflow factor times
--   the norm of the vector. Supporting theorem for `apd:thm:layer_inflow`
--   and the multi-jump recursion in `apd:rmk:multijump`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L970-L978
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L970-L978

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

theorem Lean4LPD.PauliString.norm_layerInflowMatrix_clm_le (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (w j : ℕ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖Lean4LPD.clm (layerInflowMatrix L w j) y‖
      ≤ ((((w + j * (kh - 1) : ℕ) : ℝ) * σ) ^ j / (Nat.factorial j : ℝ)) * ‖y‖ := by sorry
