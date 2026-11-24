-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_coeff_single_subst
-- name    : GlobalTheory.FormalSeries.coeff_single_subst
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:19.133617+00:00
-- url     : https://prove2.me/theorems/b274a7f3-4f5c-4519-8eaa-7ee41fffc94f
-- title:
--   Formal Series: coeff single subst
-- statement:
--   The Formal Series construction uses the coeff single subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L216-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L216-L225

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

theorem GlobalTheory.FormalSeries.coeff_single_subst [Fintype σ] {a : σ → MvPowerSeries τ S}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) (k : τ) :
    coeff (Finsupp.single k 1) (f.subst a) =
      ∑ j, coeff (Finsupp.single j 1) f • coeff (Finsupp.single k 1) (a j) := by sorry
