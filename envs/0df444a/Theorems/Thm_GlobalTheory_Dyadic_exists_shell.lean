-- Prove2me | Theorems.Thm_GlobalTheory_Dyadic_exists_shell
-- name    : GlobalTheory.Dyadic.exists_shell
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:52.746732+00:00
-- url     : https://prove2.me/theorems/4bcb5845-8b10-4f67-8741-5b60318c7cef
-- title:
--   Dyadic: exists shell
-- statement:
--   The Dyadic construction uses the exists shell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LintegralBoundByDyadicSummation.lean#L38-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LintegralBoundByDyadicSummation.lean#L38-L50

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

theorem GlobalTheory.Dyadic.exists_shell (s H : ℝ) (hH : 0 < H) :
    ∃ i : ℕ, s ≤ 2 ^ i * H ∧ (i = 0 ∨ 2 ^ i * H / 2 < s) := by sorry
