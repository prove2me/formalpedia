-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_eq_of_forall_le_order_sub
-- name    : GlobalTheory.FormalSeries.eq_of_forall_le_order_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:40.617831+00:00
-- url     : https://prove2.me/theorems/e5445970-160d-44cb-b80d-7d0aef7c3383
-- title:
--   Formal Series: eq of forall le order sub
-- statement:
--   The Formal Series construction uses the eq of forall le order sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L41-L44

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

theorem GlobalTheory.FormalSeries.eq_of_forall_le_order_sub {f g : MvPowerSeries σ R}
    (h : ∀ k : ℕ, (k : ℕ∞) ≤ (f - g).order) : f = g := by sorry
