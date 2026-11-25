-- Prove2me | Theorems.Thm_GlobalTheory_Dyadic_tsum_four
-- name    : GlobalTheory.Dyadic.tsum_four
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:04.181729+00:00
-- url     : https://prove2.me/theorems/ff805ca1-0305-4f01-bbd4-d947b53095b1
-- title:
--   Dyadic: tsum four
-- statement:
--   The Dyadic construction uses the tsum four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LintegralBoundByDyadicSummation.lean#L136-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LintegralBoundByDyadicSummation.lean#L136-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LintegralBoundByDyadicSummation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.Dyadic

theorem GlobalTheory.Dyadic.tsum_four (C : ℝ≥0∞) :
    ∑' p : ℕ × ℕ × ℕ × ℕ, C * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2)))
      = C * 16 := by sorry
