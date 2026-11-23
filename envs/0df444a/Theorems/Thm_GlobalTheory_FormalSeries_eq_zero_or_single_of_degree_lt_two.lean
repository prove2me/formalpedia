-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_eq_zero_or_single_of_degree_lt_two
-- name    : GlobalTheory.FormalSeries.eq_zero_or_single_of_degree_lt_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:10.901798+00:00
-- url     : https://prove2.me/theorems/f20139b6-5890-4b64-b6e5-330a899c1b5b
-- title:
--   Formal Series: eq zero or single of degree lt two
-- statement:
--   The Formal Series construction uses the eq zero or single of degree lt two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L46-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L46-L70

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

theorem GlobalTheory.FormalSeries.eq_zero_or_single_of_degree_lt_two {d : σ →₀ ℕ} (hd : d.degree < 2) :
    d = 0 ∨ ∃ j, d = Finsupp.single j 1 := by sorry
