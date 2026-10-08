-- Prove2me | Theorems.Thm_OAI_PiExponent_eventualLowerBound_of_not_unbounded_approximations
-- name    : OAI.PiExponent.eventualLowerBound_of_not_unbounded_approximations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:04:28.587167+00:00
-- url     : https://prove2.me/theorems/70796608-c268-4f4e-bf52-5e69e3ec9ec0
-- title:
--   No arbitrarily large exceptional denominators gives an eventual bound
-- statement:
--   Let $x$ be a real number. Assume that for each real exponent $\nu>2$, it is false that every natural threshold $Q$ admits integers $p$ and natural denominators $q\ge Q$ with $|x-p/q|\le q^{-\nu}$. Then for each $\nu>2$ there is a natural threshold $Q\ge2$ such that all integers $p$ and natural $q\ge Q$ satisfy $q^{-\nu}\le |x-p/q|$. This turns an obstruction to arbitrarily large exceptional denominators into the uniform eventual lower bound used by the irrationality-exponent criterion.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Exponent.lean#L108-L119

import Mathlib.Tactic.Push
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions

open OAI.PiExponent

theorem OAI.PiExponent.eventualLowerBound_of_not_unbounded_approximations {x : ℝ}
    (h : ∀ ν : ℝ, 2 < ν →
      ¬ ∀ Q : ℕ, ∃ (p : ℤ) (q : ℕ), Q ≤ q ∧
        |x - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-ν)) :
    EventualLowerBound x := by sorry
