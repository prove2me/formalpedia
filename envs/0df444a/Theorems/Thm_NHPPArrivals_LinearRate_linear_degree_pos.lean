-- Prove2me | Theorems.Thm_NHPPArrivals_LinearRate_linear_degree_pos
-- name    : NHPPArrivals.LinearRate.linear_degree_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:19:11.808662+00:00
-- url     : https://prove2.me/theorems/3999cea8-4165-477e-be2d-736b419c21e3
-- title:
--   THEOREM 4 (a > 0) — F has the form (14) and sup |F(t) − t| = |F(1/2) − 1/2| = rT/(8 + 4rT)
-- statement:
--   Consider the linear arrival rate $\lambda(t) = a + bt$ on $[0,T]$ with $T > 0$, $a > 0$ and $b \ge 0$, and let $r = b/a$ be its relative slope. Let $F(t) = \Lambda(tT)/\Lambda(T)$ be the conditional cdf. Then
--   $$F(t) = \frac{tT + r(tT)^2/2}{T + rT^2/2}, \qquad 0 \le t \le 1,$$
--   and the degree of nonhomogeneity is attained at $t = 1/2$:
--   $$D = \sup_{0 \le t \le 1} |F(t) - t| = |F(1/2) - 1/2| = \frac12 - \frac{T/2 + rT^2/8}{T + rT^2/2} = \frac{rT}{8 + 4rT}.$$
--
--   The formula shows that $D$ depends on the rate only through the product $rT$, and it is the building block for THEOREM 5, where it is applied to each subinterval.
--
--   **Formalization Note** $b \ge 0$ is §3.3's standing assumption ("we will assume that the arrival rate function is increasing, i.e., $b \ge 0$", p. 472); $T > 0$ is implicit in "the interval $[0,T]$". The supremum is stated as attained (`IsGreatest` of the image of $[0,1]$) and also as the value of the mission's `degree`.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, p. 472, THEOREM 4, (14), (16); standing assumption b ≥ 0, §3.3

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf

namespace NHPPArrivals.LinearRate

theorem linear_degree_pos (a b T : ℝ) (hT : 0 < T) (ha : 0 < a) (hb : 0 ≤ b) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, condCdf (linRate a b) T t =
      (t * T + (b / a) * (t * T) ^ 2 / 2) / (T + (b / a) * T ^ 2 / 2)) ∧
    IsGreatest ((fun t => |condCdf (linRate a b) T t - t|) '' Set.Icc (0:ℝ) 1)
      |condCdf (linRate a b) T (1 / 2) - 1 / 2| ∧
    degree (condCdf (linRate a b) T) = |condCdf (linRate a b) T (1 / 2) - 1 / 2| ∧
    |condCdf (linRate a b) T (1 / 2) - 1 / 2| =
      1 / 2 - (T / 2 + (b / a) * T ^ 2 / 8) / (T + (b / a) * T ^ 2 / 2) ∧
    1 / 2 - (T / 2 + (b / a) * T ^ 2 / 8) / (T + (b / a) * T ^ 2 / 2) =
      (b / a) * T / (8 + 4 * (b / a) * T) := by sorry

end NHPPArrivals.LinearRate
