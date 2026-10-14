-- Prove2me | Theorems.Thm_GreedyRS_Budget_ec2_4_tail_sum_bound
-- name    : GreedyRS.Budget.ec2_4_tail_sum_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:13.303489+00:00
-- url     : https://prove2.me/theorems/fd123d73-174a-4038-9286-dd47b2f94ffa
-- title:
--   EC.2.4, p. ec9 — C(x; n₀) − n₀ ≤ Σ_{n≥n₀} Φ̄(√n x) for x > 0
-- statement:
--   Let $Z_1, Z_2, \dots$ be i.i.d. standard normal, $\bar Z(n)$ their running average, $\tilde N(x; n_0) = \inf\{n \ge n_0 : \bar Z(n) < x\}$ the crossing time (with $\inf\emptyset = \infty$), $C(x; n_0) = \mathrm E[\tilde N(x; n_0)]$, and $\bar\Phi = 1 - \Phi$ the standard normal tail function. For every $x > 0$ and every positive integer $n_0$,
--   $$C(x; n_0) - n_0 \;\le\; \sum_{n = n_0}^{\infty} \bar\Phi\big(\sqrt n\, x\big).$$
--
--   The left side is $\mathrm E[M(x; n_0)]$ with $M(x; n_0) = \inf\{n \ge 0 : \bar Z(n + n_0) < x\}$, the number of observations beyond $n_0$ needed to cross the level $x$. The bound turns the expected crossing time into a series of normal tail probabilities, which is the first step of the proof of Lemma 6.
--
--   **Formalization Note** The inequality is stated additively, $C(x; n_0) \le n_0 + \sum_{m \ge 0} \bar\Phi(\sqrt{n_0 + m}\, x)$, in $[0, \infty]$: this avoids truncated subtraction in $[0,\infty]$ and is equivalent because $\tilde N(x; n_0) \ge n_0$. The summation index is shifted, $n = n_0 + m$. Each term $\bar\Phi(\cdot)$ lies in $[0, 1]$ and is embedded into $[0, \infty]$.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. ec9, EC.2.4 (Proof of Lemma 6), first two displays

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GreedyRS.Budget

/-- EC.2.4, p. ec9: `C(x; n0) - n0 = E[M(x; n0)] ≤ ∑_{n ≥ n0} Φ̄(√n x)` for `x > 0`, written
additively and with the summation index shifted to start at `0`. -/
theorem ec2_4_tail_sum_bound (x : ℝ) (hx : 0 < x) (n0 : ℕ) (hn0 : 1 ≤ n0) :
    GreedyRS.Greedy.Cn0 x n0 ≤ (n0 : ℝ≥0∞) + ∑' n : ℕ, ENNReal.ofReal (1 - GreedyRS.Greedy.Phi (Real.sqrt ((n0 + n : ℕ) : ℝ) * x)) := by sorry

end GreedyRS.Budget
