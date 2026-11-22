-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerStepMass_inflow
-- name    : Lean4LPD.PauliString.layerStepMass_inflow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:12.959444+00:00
-- url     : https://prove2.me/theorems/d60fc09e-99fb-4f77-a2ae-37892b35c49c
-- title:
--   Pauli String: layer Step Mass inflow
-- statement:
--   **Inflow inside a step.** One more layer increases the mass above the cutoff by at most the
--   multi-jump inflow from the lower rungs of the kept trajectory `layerN`, plus the entry factor
--   times the Pauli norm of the input. This is the inflow hypothesis of
--   `MultiLadder.sum_block_inflow_le` for `apd:eq:total_high_weight_norm`, derived here from
--   `highNorm_layerConj_le_multi`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L285-L318
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L285-L318

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

theorem Lean4LPD.PauliString.layerStepMass_inflow (layers : ℕ → List (PauliString n × ℝ))
    (Γ : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m : ℕ}
    (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a) (hm : 1 ≤ m)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (d i : ℕ) (hi : i < Γ) :
    layerStepMass layers Γ (rungWeight ko kh m) O d (i + 1) ≤
      layerStepMass layers Γ (rungWeight ko kh m) O d i +
        (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
          layerN (fun T => layers (T % Γ)) (trotterSchedule Γ (rungWeight ko kh m)) O ko kh
            (m - j) (d * Γ + i)) +
        entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a m * pauliNorm O := by sorry
