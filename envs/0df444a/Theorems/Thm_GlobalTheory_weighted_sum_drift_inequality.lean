-- Prove2me | Theorems.Thm_GlobalTheory_weighted_sum_drift_inequality
-- name    : GlobalTheory.weighted_sum_drift_inequality
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:39.026184+00:00
-- url     : https://prove2.me/theorems/f5b71e62-f70a-4ddb-a7a6-2d90cb379ca8
-- title:
--   Global Theory: weighted sum drift inequality
-- statement:
--   The Global Theory construction uses the weighted sum drift inequality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/WeightedSumDriftInequality.lean#L36-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/WeightedSumDriftInequality.lean#L36-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_WeightedSumDriftInequality
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

theorem GlobalTheory.weighted_sum_drift_inequality : (∀ (Y σ : Type) [Fintype σ] (r : ℕ) (t : σ → Y → Y) (α : ℕ → Y → ℝ) (c C B : ℝ), 0 ≤ c → c < 1 → 0 ≤ C → (∀ i ≤ r, ∀ y, 0 ≤ α i y) → (∀ y, α 0 y ≤ B ∧ α r y ≤ B) → (∀ (y : Y) (i : ℕ), 0 < i → i < r → (∑ s, α i (t s y) ≤ Fintype.card σ * (c * α i y)) ∨ ∃ j : ℕ, 0 < j ∧ j ≤ i ∧ i + j ≤ r ∧ ∀ s, α i (t s y) ≤ C * Real.sqrt (α (i - j) y * α (i + j) y)) → ∃ (e : ℕ → ℝ) (c' b : ℝ), (∀ i, 0 < e i) ∧ 0 ≤ c' ∧ c' < 1 ∧ 0 ≤ b ∧ ∀ y, ∑ s, (∑ i ∈ Finset.Ioo 0 r, e i * α i (t s y)) ≤ Fintype.card σ * (c' * (∑ i ∈ Finset.Ioo 0 r, e i * α i y) + b)) := by sorry
