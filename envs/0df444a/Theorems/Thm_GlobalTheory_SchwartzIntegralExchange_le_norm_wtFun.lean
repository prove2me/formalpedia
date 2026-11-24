-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_le_norm_wtFun
-- name    : GlobalTheory.SchwartzIntegralExchange.le_norm_wtFun
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:47:36.732342+00:00
-- url     : https://prove2.me/theorems/6084db9b-83b6-4e01-b1d8-c9a9e51d9fdd
-- title:
--   Schwartz Integral Exchange: le norm wt Fun
-- statement:
--   The Schwartz Integral Exchange construction uses the le norm wt Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIntegralSuperposition.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIntegralSuperposition.lean#L47-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open GlobalTheory.SchwartzIntegralExchange
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem GlobalTheory.SchwartzIntegralExchange.le_norm_wtFun (k n : ℕ) (w : SchwartzMap E ℂ) :
    SchwartzMap.seminorm ℂ k n w ≤ ‖wtFun k n w‖ := by sorry
