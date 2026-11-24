-- Prove2me | Theorems.Thm_GlobalTheory_Conv_eventually_lsum_ne_zero
-- name    : GlobalTheory.Conv.eventually_lsum_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:27:13.461613+00:00
-- url     : https://prove2.me/theorems/06415e34-45bf-4ba5-af24-5799ed262be6
-- title:
--   Conv: eventually lsum ne zero
-- statement:
--   The Conv construction uses the eventually lsum ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L913-L916
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L913-L916

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

theorem GlobalTheory.Conv.eventually_lsum_ne_zero {f : ℂ⸨X⸩} (hf : f ∈ convLaurent) (h0 : f ≠ 0) :
    ∀ᶠ v in 𝓝[≠] (0 : ℂ), lsum f v ≠ 0 := by sorry
