-- Prove2me | Theorems.Thm_NHPPArrivals_LinearRate_linear_degree_zero
-- name    : NHPPArrivals.LinearRate.linear_degree_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:19:52.0458+00:00
-- url     : https://prove2.me/theorems/6ce31568-b3f4-4b43-8a54-47a9bf546e52
-- title:
--   THEOREM 4 (a = 0) — F(t) = t² and D = 1/4
-- statement:
--   Consider the linear arrival rate $\lambda(t) = bt$ on $[0,T]$ with $T > 0$ and $b > 0$ (the case $a = 0$ of $\lambda(t) = a + bt$). The conditional cdf $F(t) = \Lambda(tT)/\Lambda(T)$ is
--   $$F(t) = t^2, \qquad 0 \le t \le 1,$$
--   and the degree of nonhomogeneity is
--   $$D = \sup_{0 \le t \le 1} |F(t) - t| = \frac14,$$
--   attained at $t = 1/2$.
--
--   A rate that starts at zero is therefore far from constant on any interval that starts at zero, whatever $b$ and $T$ are; in THEOREM 5 this is the first subinterval.
--
--   **Formalization Note** $b > 0$ is required: with $a = 0$ and $b = 0$ the rate is identically zero, which §3.2's assumption "strictly positive except at a finite number of points" excludes. The paper's remark that $1/4$ agrees with (16) when $r = \infty$ is not formalized.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, p. 472, THEOREM 4, (15) and "If a = 0, then D = 1/4"

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf

namespace NHPPArrivals.LinearRate

theorem linear_degree_zero (b T : ℝ) (hT : 0 < T) (hb : 0 < b) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, condCdf (linRate 0 b) T t = t ^ 2) ∧
    IsGreatest ((fun t => |condCdf (linRate 0 b) T t - t|) '' Set.Icc (0:ℝ) 1) (1 / 4) ∧
    degree (condCdf (linRate 0 b) T) = 1 / 4 := by sorry

end NHPPArrivals.LinearRate
