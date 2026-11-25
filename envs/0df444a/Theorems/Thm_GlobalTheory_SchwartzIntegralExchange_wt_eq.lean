-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_wt_eq
-- name    : GlobalTheory.SchwartzIntegralExchange.wt_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:22:00.923081+00:00
-- url     : https://prove2.me/theorems/f8d6d14c-01b1-42b2-818a-5bcc992792bf
-- title:
--   Schwartz Integral Exchange: wt eq
-- statement:
--   The Schwartz Integral Exchange construction uses the wt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIntegralSuperposition.lean#L75-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIntegralSuperposition.lean#L75-L75

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

theorem GlobalTheory.SchwartzIntegralExchange.wt_eq (k n : ℕ) (w : SchwartzMap E ℂ) : wt k n w = wtFun k n w := by sorry
