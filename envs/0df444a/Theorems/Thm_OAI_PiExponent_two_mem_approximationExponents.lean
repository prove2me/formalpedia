-- Prove2me | Theorems.Thm_OAI_PiExponent_two_mem_approximationExponents
-- name    : OAI.PiExponent.two_mem_approximationExponents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:07:34.030006+00:00
-- url     : https://prove2.me/theorems/c67d99ad-d5f8-4d1f-b110-4a9e56bc199b
-- title:
--   Every irrational real has infinitely many approximations at exponent two
-- statement:
--   For every irrational real number $x$, the exponent $2$ belongs to the set of approximation exponents: there are infinitely many distinct rational numbers $r$ whose reduced denominator is at least $2$ and whose approximation error satisfies $0<|x-r|<r.\mathrm{den}^{-2}$. This records the Dirichlet lower bound in the shared irrationality-exponent definitions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Exponent.lean#L57-L75

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions

open OAI.PiExponent

theorem OAI.PiExponent.two_mem_approximationExponents {x : ℝ} (hx : Irrational x) :
    (2 : ℝ) ∈ ApproximationExponents x := by sorry
