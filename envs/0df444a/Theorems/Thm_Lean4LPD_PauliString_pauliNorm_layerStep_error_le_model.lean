-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_layerStep_error_le_model
-- name    : Lean4LPD.PauliString.pauliNorm_layerStep_error_le_model
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:38.781364+00:00
-- url     : https://prove2.me/theorems/7acaef70-944d-4094-88e7-e11545ec3de1
-- title:
--   Pauli String: pauli Norm layer Step error le model
-- statement:
--   **The truncation error with the threshold `tZeroModel`.**
--   This is the Pauli-norm counterpart of `apd:thm:one_step_truncation_error` and
--   `apd:eq:time_condition`: the error is at most `q^(m+1) (e (m+1))^(k_o/(k_h-1)) ‖O‖` with
--   `q = decayBase Γ k_h α t = t / tZeroModel Γ k_h α`, a threshold that depends only on `Γ`, `k_h`
--   and `α`. The hypotheses `1 ≤ m` and `5 ≤ r`, under which `c₀ ≤ 2` (`cZero_le_two`), are explicit,
--   as is `B = 4eβ ≤ 1`, which also implies `β ≤ 1/2`. Since `c₀ ≤ 2` under these hypotheses,
--   `tZeroModel` is at most the threshold `tZero` with the constant `c₀` (`tZeroModel_le_tZero`), so
--   `t < tZeroModel` is the more restrictive time condition. The hypothesis `hstep` of the scalar
--   theorem `total_truncation_error_product_bound` is supplied by
--   `pauliNorm_layerStep_error_le_cZero`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L546-L575
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L546-L575

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

theorem Lean4LPD.PauliString.pauliNorm_layerStep_error_le_model
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m r : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a α t : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a)
    (hα : 0 < α) (ht : 0 ≤ t) (haA : a ≤ α * t / (r : ℝ))
    (hB : 4 * Real.exp 1 * betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a ≤ 1)
    (hadm : Admissible (r : ℝ) (m : ℝ) (Γ : ℝ)) (hm : 1 ≤ m) (hr : 5 ≤ r)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O -
        layerStepTraj layers Γ (rungWeight ko kh (m + 1)) O r) ≤
      decayBase (Γ : ℝ) (kh : ℝ) α t ^ (m + 1) *
        (Real.exp 1 * ((m : ℝ) + 1)) ^ ((ko : ℝ) / (kh - 1 : ℕ)) * pauliNorm O := by sorry
