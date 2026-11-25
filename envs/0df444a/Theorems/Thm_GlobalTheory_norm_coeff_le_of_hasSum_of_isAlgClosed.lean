-- Prove2me | Theorems.Thm_GlobalTheory_norm_coeff_le_of_hasSum_of_isAlgClosed
-- name    : GlobalTheory.norm_coeff_le_of_hasSum_of_isAlgClosed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:58.3819+00:00
-- url     : https://prove2.me/theorems/132b98f8-ca52-5ae4-98ec-239a31c21c5c
-- title:
--   Global Theory: norm coeff le of has Sum of is Alg Closed
-- statement:
--   The Global Theory construction uses the norm coeff le of has Sum of is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ResidueNormValuationSubringEqZeroIff.lean#L388-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ResidueNormValuationSubringEqZeroIff.lean#L388-L395

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Filter Topology MvPowerSeries

theorem GlobalTheory.norm_coeff_le_of_hasSum_of_isAlgClosed {C : Type*} [NontriviallyNormedField C]
    [IsUltrametricDist C] [IsAlgClosed C] {σ : Type*} {g : MvPowerSeries σ C} {f : (σ → C) → C}
    (hf : ∀ z : σ → C, (∀ i, ‖z i‖ < 1) →
      HasSum (fun t : σ →₀ ℕ => coeff t g * t.prod (z · ^ ·)) (f z)) {M : ℝ}
    (h : ∀ z : σ → C, (∀ i, ‖z i‖ < 1) → ‖f z‖ ≤ M) (t : σ →₀ ℕ) : ‖coeff t g‖ ≤ M := by sorry
