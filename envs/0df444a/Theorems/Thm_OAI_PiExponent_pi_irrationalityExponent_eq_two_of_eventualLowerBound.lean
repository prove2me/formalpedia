-- Prove2me | Theorems.Thm_OAI_PiExponent_pi_irrationalityExponent_eq_two_of_eventualLowerBound
-- name    : OAI.PiExponent.pi_irrationalityExponent_eq_two_of_eventualLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:07:24.218305+00:00
-- url     : https://prove2.me/theorems/e25cf846-f8a9-46b4-84f2-45e5eadc9701
-- title:
--   The eventual approximation bound for pi implies irrationality exponent two
-- statement:
--   Assume that for every real $\nu>2$ there is a natural threshold $Q\ge2$ such that $q^{-\nu}\le|\pi-p/q|$ for every integer numerator $p$ and natural denominator $q\ge Q$. Then the irrationality exponent of $\pi$, defined as the real supremum of the positive approximation exponents in the shared definitions, equals $2$. The eventual bound is an explicit hypothesis of this implication.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Exponent.lean#L104-L106

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions

open OAI.PiExponent

theorem OAI.PiExponent.pi_irrationalityExponent_eq_two_of_eventualLowerBound
    (h : PiEventualLowerBound) : irrationalityExponent Real.pi = 2 := by sorry
