-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_jacobian_subst
-- name    : GlobalTheory.FormalSeries.jacobian_subst
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:24.295796+00:00
-- url     : https://prove2.me/theorems/16a5076c-913d-4b02-919b-dc250bbcce02
-- title:
--   Formal Series: jacobian subst
-- statement:
--   The Formal Series construction uses the jacobian subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L227-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L227-L231

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

theorem GlobalTheory.FormalSeries.jacobian_subst [Fintype τ] {f : τ → MvPowerSeries σ R}
    (hf : ∀ s, constantCoeff (f s) = 0) (g : υ → MvPowerSeries τ R) :
    jacobian (fun i => (g i).subst f) = jacobian g * jacobian f := by sorry
