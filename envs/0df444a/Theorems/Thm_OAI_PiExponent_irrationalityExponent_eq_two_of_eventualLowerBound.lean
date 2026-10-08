-- Prove2me | Theorems.Thm_OAI_PiExponent_irrationalityExponent_eq_two_of_eventualLowerBound
-- name    : OAI.PiExponent.irrationalityExponent_eq_two_of_eventualLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:03:42.075372+00:00
-- url     : https://prove2.me/theorems/733008a0-daa2-4420-858d-db732aa4313d
-- title:
--   An eventual lower bound gives irrationality exponent two
-- statement:
--   Let $x$ be an irrational real number. Assume that for every real $\nu>2$ there is a natural threshold $Q\ge2$ such that $q^{-\nu}\le |x-p/q|$ for every integer $p$ and natural $q\ge Q$. Then the irrationality exponent defined by the shared approximation predicates is exactly $2$:
--   $$\mu(x)=2.$$
--   The exponent is the real supremum of positive exponents admitting infinitely many distinct rational approximations with reduced denominator at least $2$ and strictly positive error below $q^{-\nu}$. The upper estimate uses the assumed eventual bound; the lower estimate uses irrationality and Dirichlet approximation.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Exponent.lean#L92-L102

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions

open OAI.PiExponent

theorem OAI.PiExponent.irrationalityExponent_eq_two_of_eventualLowerBound {x : ℝ}
    (hi : Irrational x) (hx : EventualLowerBound x) :
    irrationalityExponent x = 2 := by sorry
