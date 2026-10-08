-- Prove2me | Theorems.Thm_LowerFareFirst_Critical_theorem2_critical_values_optimal
-- name    : LowerFareFirst.Critical.theorem2_critical_values_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:14.951997+00:00
-- url     : https://prove2.me/theorems/2da0cb08-1e0c-4bde-acb8-f67514e463de
-- title:
--   Theorem 2, p. 29, with §3, p. 28 — ΔZ_m(n) is decreasing, Z_m(k_m + j) satisfies (6), and rejecting class m iff n ≤ k_m is optimal
-- statement:
--   **Setting.** An aircraft on a single leg sells seats in $c \ge 2$ fare classes, numbered $1, \dots, c$ from the highest fare to the lowest, with fares $r_1 > r_2 > \cdots > r_c > 0$. Class $m$ has a random, integer-valued demand $D_m$ (the number of its future booking requests). The lower classes book first: all requests of class $m$ arrive before those of classes $1, \dots, m-1$. Assume $r_2 < r_1 P[D_1 \ge 1]$. Let $Z_m(n)$ be the expected revenue under an optimal policy when $n$ seats are empty and only classes $1, \dots, m$ may book, defined by the recursion
--   $$Z_0 \equiv 0, \qquad Z_m(n) = \mathbb E\Big[\max_{0 \le x \le \min(D_m, n)} \big(r_m x + Z_{m-1}(n-x)\big)\Big],$$
--   let $\Delta Z_m(n) = Z_m(n) - Z_m(n-1)$ for $n \ge 1$, and for $m \ge 2$ let $k_m = \max\{n \ge 1 \mid r_m < \Delta Z_{m-1}(n)\}$ (Eq. (2b)).
--
--   **Theorem.**
--
--   1. For every class $1 \le m \le c$, the marginal seat value $\Delta Z_m(n)$ is decreasing (nonincreasing) in $n \ge 1$.
--   2. For every class $2 \le m \le c$, the critical value $k_m$ exists, and
--      - (6) holds: for every $j \ge 1$,
--   $$Z_m(k_m+j) = Z_m(k_m) + \sum_{i=0}^{j-1} \Big\{ \Delta Z_{m-1}(k_m+j-i)\,P[D_m \le i] + r_m\,P[D_m \ge i+1] \Big\};$$
--      - $Z_m(n) = Z_{m-1}(n)$ for every $n \le k_m$;
--      - the critical-value rule is optimal for class $m$: rejecting a class-$m$ request if $n \le k_m$ and accepting it if $n \ge k_m + 1$ (that is, accepting $\min(D_m, (n-k_m)^+)$ requests) attains the maximum in the recursion for $Z_m(n)$, for every $n$ and every realized demand, and accepting more requests than that is strictly worse.
--
--   This is the paper's main result: an optimal seat management policy is described by one critical value per fare class, computed by (2b) and (6) class by class, and a booking request is accepted exactly when the number of empty seats exceeds the critical value of its class.
--
--   **Formalization Note.** Theorem 2 as printed states (6) and the monotonicity; the optimality of the rule and $Z_m = Z_{m-1}$ below $k_m$ are the consequences drawn in the opening paragraph of §3, included here as part of the goal. The page presupposes that the maximum in (2b) exists; here its existence is part of the conclusion. To make it exist, the fare of the lowest class is assumed positive, $r_c > 0$, an addition to the page (all fares in the paper's applications are positive). Demands need not be independent: the recursion reads only their marginal laws. "Decreasing" means nonincreasing; the strict reading is false (for instance $\Delta Z_1(n) = r_1 P[D_1 \ge n]$ is constant wherever $P[D_1 = n] = 0$).
-- source:
--   Wollmer (1992), Operations Research 40(1), Theorem 2, p. 29; §3, opening paragraph and Eq. (6), p. 28

import Mathlib
import Definitions.Def_LowerFareFirst_Critical_Model

namespace LowerFareFirst.Critical

open MeasureTheory

theorem theorem2_critical_values_optimal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (c : ℕ)
    (hM : IsSeatModel μ D r c) :
    (∀ m : ℕ, 1 ≤ m → m ≤ c → ∀ n : ℕ, 1 ≤ n → dZ μ D r m (n + 1) ≤ dZ μ D r m n) ∧
      (∀ m : ℕ, 2 ≤ m → m ≤ c → ∃ k : ℕ, IsCriticalValue μ D r m k ∧
        (∀ j : ℕ, 1 ≤ j → Z μ D r m (k + j) =
          Z μ D r m k + ∑ i ∈ Finset.range j,
            (dZ μ D r (m - 1) (k + j - i) * probLe μ D m i + r m * probGe μ D m (i + 1))) ∧
        (∀ n : ℕ, n ≤ k → Z μ D r m n = Z μ D r (m - 1) n) ∧
        CriticalRuleOptimal μ D r m k) := by sorry

end LowerFareFirst.Critical
