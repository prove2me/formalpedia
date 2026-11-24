-- Prove2me | Theorems.Thm_GlobalTheory_Conv_mem_convLaurent_of_summable
-- name    : GlobalTheory.Conv.mem_convLaurent_of_summable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:27:39.371813+00:00
-- url     : https://prove2.me/theorems/d1bc8b27-d520-48dc-911f-b4fb0aaca911
-- title:
--   Conv: mem conv Laurent of summable
-- statement:
--   The Conv construction uses the mem conv Laurent of summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L848-L852
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L848-L852

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

theorem GlobalTheory.Conv.mem_convLaurent_of_summable {f : ℂ⸨X⸩} {v : ℂ} (hv : v ≠ 0)
    (h : Summable fun n : ℤ => f.coeff n * v ^ n) : f ∈ convLaurent := by sorry
