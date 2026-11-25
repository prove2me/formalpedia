-- Prove2me | Theorems.Thm_GlobalTheory_Dyadic_exists_shell_down
-- name    : GlobalTheory.Dyadic.exists_shell_down
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:08.920738+00:00
-- url     : https://prove2.me/theorems/fa3caa5a-fbd8-4c13-a20b-d69c2216fd70
-- title:
--   Dyadic: exists shell down
-- statement:
--   The Dyadic construction uses the exists shell down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LintegralBoundByDyadicSummation.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LintegralBoundByDyadicSummation.lean#L52-L61

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

theorem GlobalTheory.Dyadic.exists_shell_down (y T : ℝ) (hy : 0 < y) (hT : y ≤ T) :
    ∃ a : ℕ, T / 2 ^ (a + 1) < y ∧ y ≤ 2 * (T / 2 ^ (a + 1)) := by sorry
