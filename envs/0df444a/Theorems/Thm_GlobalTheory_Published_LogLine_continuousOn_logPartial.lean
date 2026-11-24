-- Prove2me | Theorems.Thm_GlobalTheory_Published_LogLine_continuousOn_logPartial
-- name    : GlobalTheory.Published.LogLine.continuousOn_logPartial
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:56:42.278832+00:00
-- url     : https://prove2.me/theorems/99ebd6e9-0ad2-487b-946c-3e25518fab6c
-- title:
--   Log Line: continuous On log Partial
-- statement:
--   The Log Line construction uses the continuous On log Partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L281-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L281-L285

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.LogLine
variable {n : ℕ}

theorem GlobalTheory.Published.LogLine.continuousOn_logPartial {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n))
    (i : Fin n) {F : (Fin n → ℂ) → ℂ} (hF : DifferentiableOn ℂ F U) :
    ContinuousOn (logPartial S i F) U := by sorry
