-- Prove2me | Theorems.Thm_GlobalTheory_schwartz_weighted_sobolev_of_finrank_zero
-- name    : GlobalTheory.schwartz_weighted_sobolev_of_finrank_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:57.059089+00:00
-- url     : https://prove2.me/theorems/fe0464a1-79c4-4d3b-9b68-b5b39041c411
-- title:
--   Global Theory: schwartz weighted sobolev of finrank zero
-- statement:
--   The Global Theory construction uses the schwartz weighted sobolev of finrank zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzWeightedSobolevOfFinrankZero.lean#L8-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzWeightedSobolevOfFinrankZero.lean#L8-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzWeightedSobolevOfFinrankZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory

theorem GlobalTheory.schwartz_weighted_sobolev_of_finrank_zero :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], finrank ℝ E = 0 → ∀ (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by sorry
