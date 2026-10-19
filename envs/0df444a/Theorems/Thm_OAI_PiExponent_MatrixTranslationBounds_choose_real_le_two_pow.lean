-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_choose_real_le_two_pow
-- name    : OAI.PiExponent.MatrixTranslationBounds.choose_real_le_two_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:11:59.647287+00:00
-- url     : https://prove2.me/theorems/54830574-027b-40b6-b243-3b2d5da35063
-- title:
--   Binomial coefficients are bounded by powers of two
-- statement:
--   Every binomial coefficient of order k is at most 2 to the power k.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.choose_real_le_two_pow
    (k m : ℕ) :
    (Nat.choose k m : ℝ) ≤ (2 : ℝ) ^ k := by
  sorry
