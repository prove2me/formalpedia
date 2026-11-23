-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_le_order_subst_sub_subst
-- name    : GlobalTheory.FormalSeries.le_order_subst_sub_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:43.055562+00:00
-- url     : https://prove2.me/theorems/4c0aa083-ea87-49f9-8231-df82dbe69d12
-- title:
--   Formal Series: le order subst sub subst
-- statement:
--   The Formal Series construction uses the le order subst sub subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L162-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L162-L183

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

theorem GlobalTheory.FormalSeries.le_order_subst_sub_subst [Finite σ] {a b : σ → MvPowerSeries τ S}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) {k : ℕ}
    (hab : ∀ s, (k : ℕ∞) ≤ (a s - b s).order) {h : MvPowerSeries σ R} (hh : 2 ≤ h.order) :
    ((k + 1 : ℕ) : ℕ∞) ≤ (h.subst a - h.subst b).order := by sorry
