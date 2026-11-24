-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_continuous_iteratedFDeriv_at
-- name    : GlobalTheory.SchwartzIntegralExchange.continuous_iteratedFDeriv_at
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:48:09.977283+00:00
-- url     : https://prove2.me/theorems/2de070be-5e6a-482c-8ead-deb35d00485b
-- title:
--   Schwartz Integral Exchange: continuous iterated FDeriv at
-- statement:
--   The Schwartz Integral Exchange construction uses the continuous iterated FDeriv at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIntegralSuperposition.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIntegralSuperposition.lean#L77-L82

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

theorem GlobalTheory.SchwartzIntegralExchange.continuous_iteratedFDeriv_at (n : ℕ) (x : E) :
    Continuous (fun w : SchwartzMap E ℂ => iteratedFDeriv ℝ n w x) := by sorry
