-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_layerStep_error_le_chain
-- name    : Lean4LPD.PauliString.pauliNorm_layerStep_error_le_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:49.194914+00:00
-- url     : https://prove2.me/theorems/6e1d9d41-5e55-4423-892c-d40aac376a68
-- title:
--   Pauli String: pauli Norm layer Step error le chain
-- statement:
--   **The truncation error obeys the shifted-chain bound.**
--   This composes the norm-level triangle bound of `apd:thm:triangle` with the shifted-chain bound
--   `sum_pauliNorm_discardedLayerStep_le_chain` of `apd:eq:total_high_weight_norm`. Besides `0 < Γ`
--   and `1 ≤ m`, the hypotheses concern only the generators (layer structure, Hermiticity, sine
--   bound, `betaOf < 1`) and the locality of the observable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L465-L480
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L465-L480

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

theorem Lean4LPD.PauliString.pauliNorm_layerStep_error_le_chain
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a) (hm : 1 ≤ m)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (r : ℕ) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O -
        layerStepTraj layers Γ (rungWeight ko kh m) O r) ≤
      pauliNorm O * ∑ k ∈ range m,
        ((((r : ℝ) + 1) * Γ) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) *
          chain (epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a)
            (entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) (k + 1) m := by sorry
