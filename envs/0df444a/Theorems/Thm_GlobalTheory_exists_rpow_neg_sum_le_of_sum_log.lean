-- Prove2me | Theorems.Thm_GlobalTheory_exists_rpow_neg_sum_le_of_sum_log
-- name    : GlobalTheory.exists_rpow_neg_sum_le_of_sum_log
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:41:02.81831+00:00
-- url     : https://prove2.me/theorems/9fc845ae-be15-4840-9a4d-efe6e944e2b2
-- title:
--   Global Theory: exists rpow neg sum le of sum log
-- statement:
--   The Global Theory construction uses the exists rpow neg sum le of sum log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsRpowNegSumLeOfSumLog.lean#L25-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsRpowNegSumLeOfSumLog.lean#L25-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsRpowNegSumLeOfSumLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory

theorem GlobalTheory.exists_rpow_neg_sum_le_of_sum_log :
    (∀ (N : ℕ) (ω η : ℝ), 1 ≤ ω → 0 < η → ∃ δ c : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ ∀ (σ : Type) (S : Finset σ) (t : σ → ℝ), S.card = N → (∀ s ∈ S, ω⁻¹ ≤ t s ∧ t s ≤ ω) → η ≤ ∑ s ∈ S, Real.log (t s) → ∑ s ∈ S, t s ^ (-δ) ≤ N * c) := by sorry
