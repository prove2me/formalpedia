-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_subst_eq_linear_add
-- name    : GlobalTheory.FormalSeries.subst_eq_linear_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:15.736933+00:00
-- url     : https://prove2.me/theorems/433c98f7-057e-498f-ae66-c739044b32b5
-- title:
--   Formal Series: subst eq linear add
-- statement:
--   The Formal Series construction uses the subst eq linear add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L185-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L185-L191

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

theorem GlobalTheory.FormalSeries.subst_eq_linear_add [Fintype σ] {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (f : MvPowerSeries σ R) :
    f.subst a = ∑ j, coeff (Finsupp.single j 1) f • a j +
      (f - ∑ j, coeff (Finsupp.single j 1) f • X j).subst a := by sorry
