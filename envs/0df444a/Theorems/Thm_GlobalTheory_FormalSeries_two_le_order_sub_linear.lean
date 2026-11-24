-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_two_le_order_sub_linear
-- name    : GlobalTheory.FormalSeries.two_le_order_sub_linear
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:07.39811+00:00
-- url     : https://prove2.me/theorems/a7355d5d-7ec9-4699-80ba-39eb5dcde3b8
-- title:
--   Formal Series: two le order sub linear
-- statement:
--   The Formal Series construction uses the two le order sub linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L92-L97

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

theorem GlobalTheory.FormalSeries.two_le_order_sub_linear [Fintype σ] {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    2 ≤ (f - ∑ j, coeff (Finsupp.single j 1) f • X j).order := by sorry
