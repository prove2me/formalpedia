-- Prove2me | Theorems.Thm_LinearOptimization_no_arbitrage_iff_state_prices
-- name    : LinearOptimization.no_arbitrage_iff_state_prices
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T18:43:33.391279+00:00
-- url     : https://prove2.me/theorems/f0d04e0b-cbbf-4ab6-a292-24a034067dba
-- title:
--   Absence of arbitrage iff existence of nonnegative state prices
-- statement:
--   **(Theorem 4.8, application of Farkas' lemma to asset pricing)** A market operates for a single period in which $n$ different assets are traded, with $m$ possible states of nature at the end of the period. Investing one dollar in asset $i$ pays $r_{si}$ if the state of nature is $s$, so asset $i$ is described by a payoff vector $(r_{1i}, \dots, r_{mi})$ and the market by the $m \times n$ payoff matrix $R = (r_{si})$.
--
--   A portfolio is a vector $x = (x_1, \dots, x_n)$ whose components may be negative (short positions); it yields the state-wealth vector $w = Rx$, where
--
--   $$w_s = \sum_{i=1}^n r_{si} x_i.$$
--
--   Let $p_i$ be the price of asset $i$ and $p = (p_1, \dots, p_n)$, so acquiring $x$ costs $p'x$.
--
--   The *absence of arbitrage* condition states that any portfolio that pays off nonnegative amounts in every state of nature must have nonnegative cost: if $Rx \ge 0$, then $p'x \ge 0$.
--
--   Theorem 4.8: the absence of arbitrage condition holds if and only if there exists a nonnegative vector $q = (q_1, \dots, q_m)$ such that the price of each asset $i$ is given by
--
--   $$p_i = \sum_{s=1}^{m} q_s r_{si}.$$
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.8, p. 168

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 4.8 (p. 168).** No-arbitrage iff state prices exist:
every portfolio `x` with `Rx ≥ 0` costs `p'x ≥ 0` iff there is a
nonnegative state-price vector `q` with `pᵢ = Σ_s q_s r_{si}` for every
asset `i`. -/

theorem LinearOptimization.no_arbitrage_iff_state_prices {m n : ℕ}
    (R : Matrix (Fin m) (Fin n) ℝ) (p : Fin n → ℝ) :
    (∀ x : Fin n → ℝ, 0 ≤ R.mulVec x → 0 ≤ p ⬝ᵥ x) ↔
      ∃ q : Fin m → ℝ, 0 ≤ q ∧ ∀ i, p i = ∑ s, q s * R s i := by
  sorry
