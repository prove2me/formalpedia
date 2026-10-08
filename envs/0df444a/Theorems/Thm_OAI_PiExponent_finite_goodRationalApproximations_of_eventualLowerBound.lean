-- Prove2me | Theorems.Thm_OAI_PiExponent_finite_goodRationalApproximations_of_eventualLowerBound
-- name    : OAI.PiExponent.finite_goodRationalApproximations_of_eventualLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:07:20.064485+00:00
-- url     : https://prove2.me/theorems/1ca41a5f-a862-4d4d-a3a4-ad4c5a4fa70b
-- title:
--   Eventual lower bounds make better-than-quadratic approximations finite
-- statement:
--   Let $x$ be a real number satisfying the shared eventual lower-bound predicate, and let $\nu>2$ be real. Then only finitely many rational numbers $r$ with reduced denominator at least $2$ satisfy $0<|x-r|<r.\mathrm{den}^{-\nu}$. The hypothesis provides a bound uniform over all integer numerators and all sufficiently large natural denominators.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Exponent.lean#L77-L90

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions

open OAI.PiExponent

theorem OAI.PiExponent.finite_goodRationalApproximations_of_eventualLowerBound {x ν : ℝ}
    (hx : EventualLowerBound x) (hν : 2 < ν) :
    (GoodRationalApproximations x ν).Finite := by sorry
