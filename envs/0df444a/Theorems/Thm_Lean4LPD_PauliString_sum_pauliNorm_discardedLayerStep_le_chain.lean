-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sum_pauliNorm_discardedLayerStep_le_chain
-- name    : Lean4LPD.PauliString.sum_pauliNorm_discardedLayerStep_le_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:02:52.110474+00:00
-- url     : https://prove2.me/theorems/774c1f07-7271-48ff-b10a-e54b2690e3aa
-- title:
--   Pauli String: sum pauli Norm discarded Layer Step le chain
-- statement:
--   **The sum of the discarded Pauli norms obeys the shifted-chain bound.**
--   This is the step of `apd:eq:total_high_weight_norm` that sums the per-step inflows over the
--   layer slots, with `X_{d+1}` defined by `apd:eq:step_component`: a chain with `k + 1` jumps
--   carries the factor `((r + 1) Γ)^(k+1) / (k+1)!`. The reset and the inflow recurrence required by
--   `MultiLadder.sum_block_inflow_le` are supplied by `layerStepMass_reset` and
--   `layerStepMass_inflow`, so they are not hypotheses.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L326-L350
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L326-L350

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

theorem Lean4LPD.PauliString.sum_pauliNorm_discardedLayerStep_le_chain
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a) (hm : 1 ≤ m)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (r : ℕ) :
    (∑ d ∈ range r, pauliNorm (discardedLayerStep layers Γ (rungWeight ko kh m) O d)) ≤
      pauliNorm O * ∑ k ∈ range m,
        ((((r : ℝ) + 1) * Γ) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) *
          chain (epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a)
            (entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) (k + 1) m := by sorry
