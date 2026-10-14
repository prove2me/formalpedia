-- Prove2me | Theorems.Thm_GreedyRS_Budget_ec2_4_normal_tail_bound
-- name    : GreedyRS.Budget.ec2_4_normal_tail_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:16.077509+00:00
-- url     : https://prove2.me/theorems/62ae550d-9164-452b-b76d-2fc33123bd2c
-- title:
--   EC.2.4, p. ec9 — the normal tail bound Φ̄(t) ≤ exp(−t²/2) for t > 0
-- statement:
--   Let $\Phi$ be the standard normal cumulative distribution function and $\bar\Phi(t) = 1 - \Phi(t)$ its complement. For every $t > 0$,
--   $$\bar\Phi(t) \le \exp\!\left(-\frac{t^2}{2}\right).$$
--
--   This Chernoff-type bound is the step of the proof of Lemma 6 that turns the series of normal tail probabilities $\sum_{n \ge n_0} \bar\Phi(\sqrt n\, x)$ into a geometric series.
--
--   **Formalization Note** $\Phi$ is the cdf of the Mathlib Gaussian law with mean $0$ and variance $1$, and $\bar\Phi(t)$ is written $1 - \Phi(t)$.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. ec9, EC.2.4 (Proof of Lemma 6), sentence "Because Φ̄(x) ≤ exp(−x²/2) for x > 0"

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GreedyRS.Budget

/-- EC.2.4, p. ec9: the standard normal tail bound `Φ̄(t) ≤ exp(-t²/2)` for `t > 0`. -/
theorem ec2_4_normal_tail_bound (t : ℝ) (ht : 0 < t) :
    1 - GreedyRS.Greedy.Phi t ≤ Real.exp (-t ^ 2 / 2) := by sorry

end GreedyRS.Budget
