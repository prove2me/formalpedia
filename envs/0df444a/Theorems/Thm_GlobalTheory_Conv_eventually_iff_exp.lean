-- Prove2me | Theorems.Thm_GlobalTheory_Conv_eventually_iff_exp
-- name    : GlobalTheory.Conv.eventually_iff_exp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:23.986188+00:00
-- url     : https://prove2.me/theorems/9bfd6b2f-2e33-4641-af19-572d34f485e5
-- title:
--   Conv: eventually iff exp
-- statement:
--   The Conv construction uses the eventually iff exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L1028-L1053
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L1028-L1053

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

theorem GlobalTheory.Conv.eventually_iff_exp {p : ℂ → Prop} :
    (∀ᶠ v in 𝓝[≠] (0 : ℂ), p v) ↔
      ∃ T : ℝ, ∀ w : ℂ, T < w.im → p (Complex.exp (2 * Real.pi * Complex.I * w)) := by sorry
