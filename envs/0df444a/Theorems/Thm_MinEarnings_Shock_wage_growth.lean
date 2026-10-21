-- Prove2me | Theorems.Thm_MinEarnings_Shock_wage_growth
-- name    : MinEarnings.Shock.wage_growth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:52.862696+00:00
-- url     : https://prove2.me/theorems/72932ea2-0130-4dcc-aeaa-8eac0dd89c80
-- title:
--   Online Appendix p. 5 — after a shock u₀ < M/J(C(M)), a p = w policy has w_{t+1} ≥ ϕ(M, u₀)·w_t, hence w_t ≥ ϕ(M, u₀)^{t−1}·w₁
-- statement:
--   Let $D$, $S$ satisfy the standing assumptions with revenue maximizer $p^*$ and crossing point $w^*$, let $H$ be the inverse of $C(z) = zS(z)$ on $(0,\infty)$, let $M > 0$, and let $q \ge p^*$ satisfy $R(q) = C(M)$ (that is, $q = J(C(M))$). Let $0 < u_0 \le 1$ be a shock utilization with $u_0 < M/q$, and write $\phi = \phi(M,u_0) = M/H(R(M/u_0))$.
--
--   Consider a policy with prices equal to wages, $p_t = w_t$, which is feasible ($w_t \ge 0$), equilibrium-augmented with earnings $z_t > 0$, $z_t = w_t\,u(w_t, z_t)$, satisfies the minimum earnings rule $w_{t+1} \ge M/u(w_t, z_t)$ in every period, and starts after the shock with $w_1 \ge M/u_0$. Then for every period $t$
--   $$w_{t+1} \;\ge\; \phi(M,u_0)\, w_t, \qquad\text{and consequently}\qquad w_t \;\ge\; \phi(M,u_0)^{t-1}\, w_1 .$$
--
--   Together with $\phi(M,u_0) > 1$ this shows that the wages of such a policy are unbounded, which is the instability direction of Theorem 2.
--
--   **Formalization Note** Time is 0-based: Lean's $w_0$ is the paper's $w_1$, so the second conclusion reads $\phi^t w_0 \le w_t$ for all $t$. $J(C(M))$ is written $q$. The policy has $p = w$, the form the paper's proof reaches through its Lemma 3; Lemma 4 is not assumed but must be proved along the way. The hypothesis $u_0 \le 1$ (a utilization) is a standing pin of this mission.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), Online Appendix A, proof of Theorem 2, p. 5 (PDF 33), third paragraph

import Mathlib
import Definitions.Def_MinEarnings_Shock_Setting

namespace MinEarnings.Shock

theorem wage_growth (D S H : ℝ → ℝ) (pStar wStar M u₀ q : ℝ)
    (hA : MinEarnings.Threshold.Assumptions D S pStar wStar) (hH : MinEarnings.Threshold.IsCostInverse S H) (hM : 0 < M) (hu₀ : 0 < u₀)
    (hu₀1 : u₀ ≤ 1) (hq : pStar ≤ q) (hRq : MinEarnings.Threshold.revenue D q = MinEarnings.Threshold.cost S M) (hlt : u₀ < M / q)
    (w z : ℕ → ℝ) (hfeas : MinEarnings.Threshold.IsFeasible w w) (heq : MinEarnings.Threshold.IsEquilibrium D S w w z)
    (hrule : MinEarnings.Threshold.MinEarningsRule D S M w w z) (hw0 : M / u₀ ≤ w 0) :
    (∀ t, M / H (MinEarnings.Threshold.revenue D (M / u₀)) * w t ≤ w (t + 1)) ∧
      ∀ t, (M / H (MinEarnings.Threshold.revenue D (M / u₀))) ^ t * w 0 ≤ w t := by sorry

end MinEarnings.Shock
