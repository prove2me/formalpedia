-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_norm_layerInflowMatrix_le_factorial
-- name    : Lean4LPD.PauliString.norm_layerInflowMatrix_le_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:13.015474+00:00
-- url     : https://prove2.me/theorems/7722c75b-5470-4b8b-b83a-d354dce76855
-- title:
--   Pauli String: norm layer Inflow Matrix le factorial
-- statement:
--   **Layer inflow, factorial form.** Formalizes the second inequality of
--   `apd:eq:layer_inflow`, `C(W, j) σ^j ≤ (W σ)^j / j!` with `W = w + j (k_h - 1)`, for the
--   absolute-sine parameter `σ` and an arbitrary natural weight threshold `w`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L841-L852
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L841-L852

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

theorem Lean4LPD.PauliString.norm_layerInflowMatrix_le_factorial (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (w j : ℕ) :
    ‖layerInflowMatrix L w j‖
      ≤ (((w + j * (kh - 1) : ℕ) : ℝ) * σ) ^ j / (Nat.factorial j : ℝ) := by sorry
