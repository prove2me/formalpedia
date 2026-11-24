-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_Model_neg_one_not_sq_sqrt_two
-- name    : GlobalTheory.QuadSymbol.Model.neg_one_not_sq_sqrt_two
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:09:41.992232+00:00
-- url     : https://prove2.me/theorems/448c8746-c457-4679-a823-0b36231b5330
-- title:
--   Model: neg one not sq sqrt two
-- statement:
--   The Model construction uses the neg one not sq sqrt two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L143-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory.QuadSymbol
open GlobalTheory GlobalTheory.QuadSymbol GlobalTheory.QuadSymbol.Model

theorem GlobalTheory.QuadSymbol.Model.neg_one_not_sq_sqrt_two (r : QuadraticAlgebra ℚ 2 0) : r ^ 2 ≠ -1 + 0 * r := by sorry
