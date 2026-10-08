-- Prove2me | Theorems.Thm_OAI_PiExponent_eventualLowerBound_iff_integer
-- name    : OAI.PiExponent.eventualLowerBound_iff_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:02:27.212384+00:00
-- url     : https://prove2.me/theorems/f6226cea-1cdb-4891-8f38-f628fef25206
-- title:
--   Equivalent natural and integer denominator formulations
-- statement:
--   For every real number $x$, the eventual lower bound at every exponent $\nu>2$ is equivalent whether its threshold and denominators are natural numbers or integers. In both formulations the threshold is at least $2$, the numerator is an arbitrary integer, and the bound is uniform in the numerator:
--   $$q^{-\nu}\le |x-p/q|\qquad(q\ge Q).$$
--   This conversion preserves the non-strict approximation inequality and allows results using integer denominators to be reused with natural denominator statements.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Exponent.lean#L7-L26

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions

open OAI.PiExponent

theorem OAI.PiExponent.eventualLowerBound_iff_integer (x : ℝ) :
    EventualLowerBound x ↔ IntegerEventualLowerBound x := by sorry
