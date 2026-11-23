-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_two_le_order_iff
-- name    : GlobalTheory.FormalSeries.two_le_order_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:38.264314+00:00
-- url     : https://prove2.me/theorems/1bbdf53e-a8f1-4eb2-be6d-54a473957a60
-- title:
--   Formal Series: two le order iff
-- statement:
--   The Formal Series construction uses the two le order iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L72-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L72-L90

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

theorem GlobalTheory.FormalSeries.two_le_order_iff {f : MvPowerSeries σ R} :
    2 ≤ f.order ↔ constantCoeff f = 0 ∧ ∀ j, coeff (Finsupp.single j 1) f = 0 := by sorry
