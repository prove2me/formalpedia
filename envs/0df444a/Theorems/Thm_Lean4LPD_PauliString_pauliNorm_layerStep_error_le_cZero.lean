-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_layerStep_error_le_cZero
-- name    : Lean4LPD.PauliString.pauliNorm_layerStep_error_le_cZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:16.668398+00:00
-- url     : https://prove2.me/theorems/b7283cf9-4f8b-4b3b-8695-a487fc402abd
-- title:
--   Pauli String: pauli Norm layer Step error le c Zero
-- statement:
--   The truncation error obeys the `c₀` bound
--   (`apd:thm:triangle`; `apd:eq:total_high_weight_norm`; `apd:eq:c0`).
--   This is a statement in the normalized Pauli norm, not about expectation values.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L518-L534
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L518-L534

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}

theorem Lean4LPD.PauliString.pauliNorm_layerStep_error_le_cZero
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m r : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a A : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a ≤ 1 / 2)
    (hA : 0 ≤ A) (hr : 1 ≤ r) (haA : a ≤ A / (r : ℝ))
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O -
        layerStepTraj layers Γ (rungWeight ko kh (m + 1)) O r) ≤
      (cZero (r : ℝ) (m : ℝ) (Γ : ℝ)
          (4 * Real.exp 1 * betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) * Γ * A) ^ (m + 1) *
        (∏ j ∈ range (m + 1), rungW (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) (j + 2)) /
          (Nat.factorial (m + 1) : ℝ) * pauliNorm O := by sorry
