-- Prove2me | Theorems.Thm_GlobalTheory_exists_pos_finite_density_of_almost_translation_invariant
-- name    : GlobalTheory.exists_pos_finite_density_of_almost_translation_invariant
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:36:18.287938+00:00
-- url     : https://prove2.me/theorems/c5f6eceb-bdc9-4dff-9770-d4c35983782f
-- title:
--   Global Theory: exists pos finite density of almost translation invariant
-- statement:
--   The Global Theory construction uses the exists pos finite density of almost translation invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsPosFiniteDensityOfAlmostTranslationInvaria.lean#L99-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsPosFiniteDensityOfAlmostTranslationInvaria.lean#L99-L256

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsPosFiniteDensityOfAlmostTranslationInvaria
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Metric Set
open GlobalTheory
open MeasureTheory Filter Topology Metric Set

theorem GlobalTheory.exists_pos_finite_density_of_almost_translation_invariant :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (lam ν : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure ν], (∀ r : ℝ, 0 < r → ν (ball 0 r) ≠ 0) → (∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ ball (0 : V) δ, ∀ r ∈ Ioo (0 : ℝ) δ, ν (ball 0 r) ≤ ν (ball x (κ * r)) ∧ ν (ball x r) ≤ ν (ball 0 (κ * r))) → ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ Tendsto (fun r : ℝ => ν (ball 0 r) / lam (ball 0 r)) (𝓝[>] 0) (𝓝 c) := by sorry
