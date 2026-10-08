-- Prove2me | Theorems.Thm_LowerFareFirst_Critical_sec3_rejection_rule
-- name    : LowerFareFirst.Critical.sec3_rejection_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:23.811375+00:00
-- url     : https://prove2.me/theorems/0ac0be9c-6558-40ee-a1b2-3b1c3c7f7b40
-- title:
--   §3, p. 28; proof of Lemma 1, p. 29 — if ΔZ_{m−1} is decreasing, rejecting class m iff n ≤ k_m is optimal, and Z_m = Z_{m−1} on n ≤ k_m
-- statement:
--   Consider the seat management model with lower fare classes booking first under the standing assumptions of §1: fares $r_1 > \cdots > r_c > 0$, integer-valued demands $D_m$ on a probability space, $r_2 < r_1 P[D_1 \ge 1]$, and optimal values
--   $$Z_0 \equiv 0, \qquad Z_m(n) = \mathbb E\Big[\max_{0 \le x \le \min(D_m, n)} \big(r_m x + Z_{m-1}(n-x)\big)\Big].$$
--   Fix a class $m$ with $2 \le m \le c$, suppose that $\Delta Z_{m-1}(n) = Z_{m-1}(n) - Z_{m-1}(n-1)$ is decreasing (nonincreasing) in $n \ge 1$, and let $k = k_m$ be the critical value of class $m$ from (2b). Then:
--
--   1. The critical-value rule is optimal for class $m$: for every number $n$ of empty seats, every realized demand $d$ of class $m$ and every $x \le \min(d, n)$,
--   $$r_m x + Z_{m-1}(n-x) \le r_m x^\ast + Z_{m-1}(n - x^\ast), \qquad x^\ast = \min\big(d, (n - k_m)^+\big),$$
--   with strict inequality when $x > (n - k_m)^+$. In words: reject a class-$m$ request if $n \le k_m$ and accept it if $n \ge k_m + 1$.
--   2. $Z_m(n) = Z_{m-1}(n)$ for all $n \le k_m$, because all class-$m$ requests are rejected there.
--
--   This is the step of the paper's induction that turns the monotonicity of the marginal seat value of the higher classes into the optimality of a threshold policy for the next class down.
--
--   **Formalization Note.** The paper's §3 sentence says "all reservation requests for class $m + 1$ are rejected"; class $m$ is meant, as the surrounding sentences and the proof of Lemma 1 (with $\bar m + 1$ in place of $m$) show. "Optimal" is formalized as attaining the maximum in the recursion for $Z_m$, realization by realization.
-- source:
--   Wollmer (1992), Operations Research 40(1), §3, opening paragraph, p. 28; proof of Lemma 1, first two sentences, p. 29

import Mathlib
import Definitions.Def_LowerFareFirst_Critical_Model

namespace LowerFareFirst.Critical

open MeasureTheory

theorem sec3_rejection_rule {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (c : ℕ)
    (hM : IsSeatModel μ D r c)
    (m k : ℕ) (hm : 2 ≤ m) (hmc : m ≤ c)
    (hdec : ∀ n : ℕ, 1 ≤ n → dZ μ D r (m - 1) (n + 1) ≤ dZ μ D r (m - 1) n)
    (hk : IsCriticalValue μ D r m k) :
    CriticalRuleOptimal μ D r m k ∧ ∀ n : ℕ, n ≤ k → Z μ D r m n = Z μ D r (m - 1) n := by sorry

end LowerFareFirst.Critical
