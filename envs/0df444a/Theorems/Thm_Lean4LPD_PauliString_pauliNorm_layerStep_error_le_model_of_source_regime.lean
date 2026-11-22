-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_layerStep_error_le_model_of_source_regime
-- name    : Lean4LPD.PauliString.pauliNorm_layerStep_error_le_model_of_source_regime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:54.904016+00:00
-- url     : https://prove2.me/theorems/078b2923-d5cf-4bb1-a39a-e49cf35216cb
-- title:
--   Pauli String: pauli Norm layer Step error le model of source regime
-- statement:
--   **The norm-level truncation bound in the paper's parameter regime.**
--   This is `apd:thm:one_step_truncation_error` with `apd:eq:time_condition` at the level of the
--   normalized Pauli norm. Let `O` be `k_o`-local, let each step consist of `Γ` disjoint-support
--   layers of Hermitian rotations of weight at most `k_h`, `2 ≤ k_h`, with
--   `|sin θ| ≤ a ≤ α t / r`, and let the cutoff be `w* = k_o + m (k_h - 1)`. If `Admissible r m Γ`
--   (in particular `m ≤ r` and `8 (m + 1)² ≤ r Γ`), `1 ≤ m`, `5 ≤ r` and
--   `r ≥ 8e² (k_o + k_h - 1) α t`, then
--
--     `‖U^r(O) - O_r‖ ≤ (t / t₀)^(m+1) · (e (m+1))^(k_o/(k_h-1)) · ‖O‖`,  `t₀ = tZeroModel Γ k_h α`.
--
--   The step-count condition gives `B = 4eβ ≤ 1` (`source_entry_inflation_le_one`) and hence
--   `β ≤ 1/2`, so neither is a separate hypothesis. The base `t / t₀` is below one whenever
--   `t < tZeroModel Γ k_h α`, by `decayBase_lt_one`. Nothing is asserted about expectation values in
--   a state or about the Trotter approximation of the Hamiltonian evolution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L591-L616
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L591-L616

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

theorem Lean4LPD.PauliString.pauliNorm_layerStep_error_le_model_of_source_regime
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m r : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a α t : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a)
    (hα : 0 < α) (ht : 0 ≤ t) (haA : a ≤ α * t / (r : ℝ))
    (hsteps : 8 * (Real.exp 1) ^ 2 * ((ko : ℝ) + kh - 1) * α * t ≤ (r : ℝ))
    (hadm : Admissible (r : ℝ) (m : ℝ) (Γ : ℝ)) (hm : 1 ≤ m) (hr : 5 ≤ r)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O -
        layerStepTraj layers Γ (rungWeight ko kh (m + 1)) O r) ≤
      decayBase (Γ : ℝ) (kh : ℝ) α t ^ (m + 1) *
        (Real.exp 1 * ((m : ℝ) + 1)) ^ ((ko : ℝ) / (kh - 1 : ℕ)) * pauliNorm O := by sorry
