-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_poisson_tv_hellinger_bound
-- name    : LindbladTolerant.Testing.poisson_tv_hellinger_bound
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:03:43.926177+00:00
-- url     : https://prove2.me/theorems/8fc44a5f-ce75-4997-a32c-36ec9bad07c0
-- title:
--   Theorem 5.2 — Poisson total variation via Hellinger affinity
-- statement:
--   For $a,b\ge0$, let $p_a$ and $p_b$ be the probability mass functions of $\operatorname{Pois}(a)$ and $\operatorname{Pois}(b)$. Their total variation distance satisfies
--   $$
--   d_{\mathrm{TV}}(p_a,p_b)
--    \le \sqrt{1-\exp\!\left[-(\sqrt b-\sqrt a)^2\right]}.
--   $$
--
--   Indeed, the exponential-series calculation gives the Hellinger affinity
--   $$
--   A_H(p_a,p_b)=\sum_{r=0}^{\infty}\sqrt{p_a(r)p_b(r)}
--    =\exp\!\left[-\frac12(\sqrt b-\sqrt a)^2\right],
--   $$
--   and factoring $p_a-p_b$ into square roots followed by Cauchy–Schwarz yields
--   $$
--   d_{\mathrm{TV}}(p_a,p_b)\le\sqrt{1-A_H(p_a,p_b)^2}.
--   $$
--
--   Both means may be zero. This is the exact inequality used immediately before Eq.(118) in the time lower bound.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238, Theorem 5.2 proof, Eqs.(116)–(118), pp.29–30. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf

import Definitions.Def_LindbladTolerant_Testing_lower_bound_model

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix ENNReal

namespace LindbladTolerant.Testing

theorem poisson_tv_hellinger_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    poissonTV a b ≤ Real.sqrt (1 - Real.exp (-(Real.sqrt b - Real.sqrt a)^2)) := by sorry
