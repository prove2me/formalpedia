-- Prove2me | Theorems.Thm_GlobalTheory_Conv_mem_convSeries_of_summable
-- name    : GlobalTheory.Conv.mem_convSeries_of_summable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:30.456075+00:00
-- url     : https://prove2.me/theorems/fb0a4621-c7c2-46a8-a4a6-9e103e2f3ee6
-- title:
--   Conv: mem conv Series of summable
-- statement:
--   The Conv construction uses the mem conv Series of summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L201-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L201-L206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology ENNReal NNReal ContDiff
open Filter Metric
noncomputable section
open GlobalTheory GlobalTheory.Conv

theorem GlobalTheory.Conv.mem_convSeries_of_summable {f : ℂ⟦X⟧} {u : ℂ} (hu : u ≠ 0)
    (h : Summable fun n => PowerSeries.coeff n f * u ^ n) : f ∈ convSeries := by sorry
