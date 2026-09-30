-- Prove2me | Theorems.Thm_Goldbach_exceptional_set_power_saving
-- name    : Goldbach.exceptional_set_power_saving
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-12T04:07:56.57849+00:00
-- url     : https://prove2.me/theorems/f011e237-b2e3-4d04-93d4-fc9e3a980651
-- title:
--   Montgomery–Vaughan: $E(x) \ll x^{1-\delta}$
-- statement:
--   The number $E(x)$ of even integers $4 \le n \le x$ that are not a sum of two primes satisfies $E(x) \ll x^{1-\delta}$ for some absolute $\delta > 0$ and absolute constant $C$.
--
--   This is the Montgomery–Vaughan exceptional-set theorem (1975): the circle method applied to binary Goldbach does prove the conjecture for almost all even numbers, since on major arcs the singular series is bounded below and the major-arc mass is correct; failures are confined to a power-saving exceptional set. The current best exponent is $\delta$ near $1/2$ (Pintz). A power-saving exceptional set can in principle contain an unbounded tail, so this does not yield $\texttt{even\_goldbach\_above\_4e18}$.
-- source:
--   H. L. Montgomery and R. C. Vaughan, The exceptional set in Goldbach's problem, Acta Arithmetica 27 (1975), 353-370

import Mathlib

namespace Goldbach

theorem exceptional_set_power_saving :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 1 ≤ x →
      ((Set.ncard {n : ℕ | 4 ≤ n ∧ n ≤ Nat.floor x ∧ Even n ∧
        ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q}) : ℝ)
        ≤ C * x ^ (1 - δ) := by
  sorry

end Goldbach
