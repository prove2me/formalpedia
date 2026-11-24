-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_le_order_sub
-- name    : GlobalTheory.FormalSeries.le_order_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:19.134628+00:00
-- url     : https://prove2.me/theorems/2ae27f6c-6263-4d6a-961c-c3cf6202f8cf
-- title:
--   Formal Series: le order sub
-- statement:
--   The Formal Series construction uses the le order sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L26-L28

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

theorem GlobalTheory.FormalSeries.le_order_sub {k : ℕ∞} {f g : MvPowerSeries σ R} (hf : k ≤ f.order) (hg : k ≤ g.order) :
    k ≤ (f - g).order := by sorry
