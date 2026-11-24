-- Prove2me | Theorems.Thm_GlobalTheory_Published_LogLine_offDivisor_mono
-- name    : GlobalTheory.Published.LogLine.offDivisor_mono
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:56:28.879834+00:00
-- url     : https://prove2.me/theorems/6204758c-aff3-4f02-a6e6-e8315c0c820e
-- title:
--   Log Line: off Divisor mono
-- statement:
--   The Log Line construction uses the off Divisor mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L52-L53

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

theorem GlobalTheory.Published.LogLine.offDivisor_mono {U V : Set (Fin n → ℂ)} (h : U ⊆ V) (S : Finset (Fin n)) :
    offDivisor U S ⊆ offDivisor V S := by sorry
