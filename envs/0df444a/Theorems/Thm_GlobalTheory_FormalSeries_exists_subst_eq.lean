-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_exists_subst_eq
-- name    : GlobalTheory.FormalSeries.exists_subst_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:19.742559+00:00
-- url     : https://prove2.me/theorems/de0dda8d-a999-44f9-a11e-1aa1665a2496
-- title:
--   Formal Series: exists subst eq
-- statement:
--   The Formal Series construction uses the exists subst eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L287-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L287-L334

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

theorem GlobalTheory.FormalSeries.exists_subst_eq [Fintype σ] [Fintype τ] [DecidableEq τ] {u : τ → MvPowerSeries σ R}
    (hu : ∀ i, constantCoeff (u i) = 0) {B : Matrix σ τ R} (hB : jacobian u * B = 1)
    {c : τ → MvPowerSeries υ R} (hc : ∀ i, constantCoeff (c i) = 0) :
    ∃ v : σ → MvPowerSeries υ R, (∀ j, constantCoeff (v j) = 0) ∧ ∀ i, (u i).subst v = c i := by sorry
