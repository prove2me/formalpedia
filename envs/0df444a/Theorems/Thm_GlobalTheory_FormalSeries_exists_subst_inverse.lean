-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_exists_subst_inverse
-- name    : GlobalTheory.FormalSeries.exists_subst_inverse
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:32.781945+00:00
-- url     : https://prove2.me/theorems/da124535-e6c4-48fb-b61d-6760fe11f518
-- title:
--   Formal Series: exists subst inverse
-- statement:
--   The Formal Series construction uses the exists subst inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L336-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L336-L362

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

theorem GlobalTheory.FormalSeries.exists_subst_inverse [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
    {u : τ → MvPowerSeries σ R} (hu : ∀ i, constantCoeff (u i) = 0) {B : Matrix σ τ R}
    (hB : jacobian u * B = 1) (hB' : B * jacobian u = 1) :
    ∃ v : σ → MvPowerSeries τ R, (∀ j, constantCoeff (v j) = 0) ∧
      (∀ i, (u i).subst v = X i) ∧ ∀ j, (v j).subst u = X j := by sorry
