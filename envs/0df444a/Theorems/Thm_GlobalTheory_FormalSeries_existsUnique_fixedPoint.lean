-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_existsUnique_fixedPoint
-- name    : GlobalTheory.FormalSeries.existsUnique_fixedPoint
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:02.996629+00:00
-- url     : https://prove2.me/theorems/996dd12c-8e14-4de5-bbfc-2a87a37e5a8c
-- title:
--   Formal Series: exists Unique fixed Point
-- statement:
--   The Formal Series construction uses the exists Unique fixed Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L233-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L233-L285

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]
variable [Algebra R S]

theorem GlobalTheory.FormalSeries.existsUnique_fixedPoint (Φ : (σ → MvPowerSeries τ S) → (σ → MvPowerSeries τ S))
    (h0 : ∀ a, (∀ s, constantCoeff (a s) = 0) → ∀ s, constantCoeff (Φ a s) = 0)
    (hΦ : ∀ a b (k : ℕ), (∀ s, constantCoeff (a s) = 0) → (∀ s, constantCoeff (b s) = 0) →
      (∀ s, (k : ℕ∞) ≤ (a s - b s).order) → ∀ s, ((k + 1 : ℕ) : ℕ∞) ≤ (Φ a s - Φ b s).order) :
    ∃! a, (∀ s, constantCoeff (a s) = 0) ∧ Φ a = a := by sorry
