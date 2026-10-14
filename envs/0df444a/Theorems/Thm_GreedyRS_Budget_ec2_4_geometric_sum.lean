-- Prove2me | Theorems.Thm_GreedyRS_Budget_ec2_4_geometric_sum
-- name    : GreedyRS.Budget.ec2_4_geometric_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:57.236315+00:00
-- url     : https://prove2.me/theorems/88b717a9-54fe-45e6-a04b-5d834dfbc410
-- title:
--   EC.2.4, p. ec9 — Σ_{n≥n₀} exp(−nx²/2) = exp(−n₀x²/2)/(1 − exp(−x²/2)) for x ≠ 0
-- statement:
--   For every real $x \ne 0$ and every nonnegative integer $n_0$,
--   $$\sum_{n = n_0}^{\infty} \exp\!\left(-\frac{n x^2}{2}\right) = \frac{\exp(-n_0 x^2/2)}{1 - \exp(-x^2/2)}.$$
--
--   This is the closed form of the geometric series that appears at the end of the proof of Lemma 6; combined with the tail-sum bound and the normal tail bound it gives $C(x; n_0) - n_0 \le e^{-n_0 x^2/2}/(1 - e^{-x^2/2})$.
--
--   **Formalization Note** The summation index is shifted, $n = n_0 + m$ with $m \ge 0$, and the sum is the real-valued `tsum`; the series converges because $x \ne 0$ makes the ratio $e^{-x^2/2}$ lie in $(0, 1)$.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. ec9, EC.2.4 (Proof of Lemma 6), third display (the equality)

import Mathlib

namespace GreedyRS.Budget

/-- EC.2.4, p. ec9: `∑_{n ≥ n0} exp(-n x²/2) = exp(-n0 x²/2) / (1 - exp(-x²/2))` for `x ≠ 0`,
with the summation index shifted to start at `0`. -/
theorem ec2_4_geometric_sum (x : ℝ) (hx : x ≠ 0) (n0 : ℕ) :
    ∑' n : ℕ, Real.exp (-((n0 + n : ℕ) : ℝ) * x ^ 2 / 2) =
      Real.exp (-(n0 : ℝ) * x ^ 2 / 2) / (1 - Real.exp (-x ^ 2 / 2)) := by sorry

end GreedyRS.Budget
