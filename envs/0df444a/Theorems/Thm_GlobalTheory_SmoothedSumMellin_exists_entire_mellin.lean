-- Prove2me | Theorems.Thm_GlobalTheory_SmoothedSumMellin_exists_entire_mellin
-- name    : GlobalTheory.SmoothedSumMellin.exists_entire_mellin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:18:35.160686+00:00
-- url     : https://prove2.me/theorems/c0d0d5c8-dcd8-4b0f-968b-e5dc4385c80f
-- title:
--   Smoothed Sum Mellin: exists entire mellin
-- statement:
--   The Smoothed Sum Mellin construction uses the exists entire mellin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEntireMellinSmoothedDirichletSum.lean#L153-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEntireMellinSmoothedDirichletSum.lean#L153-L245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEntireMellinSmoothedDirichletSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open Set Filter Asymptotics Topology
open GlobalTheory GlobalTheory.SmoothedSumMellin

theorem GlobalTheory.SmoothedSumMellin.exists_entire_mellin : ∀ (ι : Type) [Countable ι] (a : ι → ℂ) (N : ι → ℝ) (R : ℂ) (wt : ℝ → ℂ), ContDiff ℝ ∞ wt → (∃ a b : ℝ, 0 < a ∧ ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) → (∀ i, a i ≠ 0 → 1 ≤ N i) → (∀ σ : ℝ, 1 < σ → Summable fun i => ‖a i‖ * N i ^ (-σ)) → (∀ A : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖∑' i, a i * wt (t * N i) - R / (t : ℂ)‖ ≤ C * t ^ A) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = R ∧ ∀ s : ℂ, 1 < s.re → Z s = mellin wt s * ((s - 1) * ∑' i, a i * (N i : ℂ) ^ (-s)) := by sorry
