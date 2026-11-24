-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_le_order_sum
-- name    : GlobalTheory.FormalSeries.le_order_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:14.339596+00:00
-- url     : https://prove2.me/theorems/a9f09a59-7ce8-477f-9e8c-41d1d9f9a479
-- title:
--   Formal Series: le order sum
-- statement:
--   The Formal Series construction uses the le order sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L30-L33

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

theorem GlobalTheory.FormalSeries.le_order_sum {ι : Type*} {k : ℕ∞} (s : Finset ι) {f : ι → MvPowerSeries σ R}
    (hf : ∀ i ∈ s, k ≤ (f i).order) : k ≤ (∑ i ∈ s, f i).order := by sorry
