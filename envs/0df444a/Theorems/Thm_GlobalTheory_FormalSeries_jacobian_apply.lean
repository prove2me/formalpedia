-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
-- name    : GlobalTheory.FormalSeries.jacobian_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:20.832294+00:00
-- url     : https://prove2.me/theorems/3d4ef589-fd20-4ba0-9d55-169767883b29
-- title:
--   Formal Series: jacobian apply
-- statement:
--   The Formal Series construction uses the jacobian apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L15-L16

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

theorem GlobalTheory.FormalSeries.jacobian_apply (f : τ → MvPowerSeries σ R) (i : τ) (j : σ) :
    jacobian f i j = coeff (Finsupp.single j 1) (f i) := by sorry

attribute [defeq] GlobalTheory.FormalSeries.jacobian_apply
