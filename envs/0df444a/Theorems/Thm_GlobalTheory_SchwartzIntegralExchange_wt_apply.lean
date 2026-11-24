-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_wt_apply
-- name    : GlobalTheory.SchwartzIntegralExchange.wt_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:48.779405+00:00
-- url     : https://prove2.me/theorems/6bdb01b2-599e-439c-bddb-f3e39702fbf3
-- title:
--   Schwartz Integral Exchange: wt apply
-- statement:
--   The Schwartz Integral Exchange construction uses the wt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIntegralSuperposition.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIntegralSuperposition.lean#L72-L73

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

theorem GlobalTheory.SchwartzIntegralExchange.wt_apply (k n : ℕ) (w : SchwartzMap E ℂ) (x : E) :
    wt k n w x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n w x := by sorry
