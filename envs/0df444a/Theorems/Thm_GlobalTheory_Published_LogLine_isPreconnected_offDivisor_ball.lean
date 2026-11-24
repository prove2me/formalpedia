-- Prove2me | Theorems.Thm_GlobalTheory_Published_LogLine_isPreconnected_offDivisor_ball
-- name    : GlobalTheory.Published.LogLine.isPreconnected_offDivisor_ball
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:57:04.393848+00:00
-- url     : https://prove2.me/theorems/0e4c4247-00d5-4c82-aafd-ccfaef30d96e
-- title:
--   Log Line: is Preconnected off Divisor ball
-- statement:
--   The Log Line construction uses the is Preconnected off Divisor ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L92-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L92-L116

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

theorem GlobalTheory.Published.LogLine.isPreconnected_offDivisor_ball (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) (S : Finset (Fin n)) :
    IsPreconnected (offDivisor (ball c r) S) := by sorry
