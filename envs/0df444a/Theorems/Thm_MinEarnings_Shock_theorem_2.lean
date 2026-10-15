-- Prove2me | Theorems.Thm_MinEarnings_Shock_theorem_2
-- name    : MinEarnings.Shock.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:40.811687+00:00
-- url     : https://prove2.me/theorems/a1ec3f1f-b601-4c3a-a805-850a0a661e2c
-- title:
--   Theorem 2, p. 13 — an M-minimum-earnings marketplace absorbs a u₀ utilization shock iff u₀ ≥ M/J(C(M))
-- statement:
--   Let $D$ and $S$ be demand and supply curves satisfying the regularity assumptions, with revenue $R(p) = pD(p)$ unimodal with its maximum at $p^* \ge 0$ (strictly increasing on $[0,p^*]$, strictly decreasing on $[p^*,\infty)$), cost $C(z) = zS(z)$, and crossing point $w^* \ge 0$ with $D(w^*) = S(w^*)$. Let $M > 0$ be the minimum hourly earnings target, and let $J$ be the inverse of $R$ on its decreasing branch: $J(r) = p$ iff $p \ge p^*$ and $R(p) = r$. Write $q = J(C(M))$, i.e. $q \ge p^*$ and $R(q) = C(M)$.
--
--   For a shock utilization $0 < u_0 \le 1$, the $M$-minimum-earnings marketplace is able to absorb the $u_0$ utilization shock — some feasible equilibrium-augmented policy obeying the minimum earnings rule, with first wage $w_1 \ge M/u_0$, has bounded wages and non-negative profit in every period — if and only if
--   $$u_0 \;\ge\; \frac{M}{J(C(M))}.$$
--
--   The threshold $M/J(C(M))$ is the lowest utilization at which an unsubsidized platform can still pay the wage $M/u_0$ that the rule imposes after the shock without losing money; below it, the rule ratchets wages up geometrically.
--
--   **Formalization Note** $J(C(M))$ is written $q$: the theorem is stated for a price $q \ge p^*$ with $R(q) = C(M)$, which is unique by strict decrease of $R$ on $[p^*,\infty)$; it does not assert that such a $q$ exists (that needs $C(M) \le R(p^*)$; the paper's domain $(0, R(p^*)]$ for $J$ moreover presumes $R(p) \to 0$ as $p \to \infty$, which is not among its assumptions). The shock utilization is pinned to $0 < u_0 \le 1$: $u_0$ is a utilization, and without $u_0 \le 1$ the "if" direction fails when $p^* \le w^* < M$. Time is 0-based, so $w_1 \ge M/u_0$ is a condition on Lean's first wage $w_0$. Equilibrium-augmented policies have positive earnings $z_t > 0$, which excludes Lean's junk utilization $0/0 = 0$. Boundedness is $\exists B\,\forall t,\ w_t \le B$, and profit is non-negative in all periods, as Definition 3 requires.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), p. 13, Theorem 2 (with Definition 3 and J, p. 13); proof Online Appendix A, p. 5 (PDF 33)

import Mathlib
import Definitions.Def_MinEarnings_Shock_Setting

namespace MinEarnings.Shock

theorem theorem_2 (D S : ℝ → ℝ) (pStar wStar M u₀ q : ℝ) (hA : MinEarnings.Threshold.Assumptions D S pStar wStar)
    (hM : 0 < M) (hu₀ : 0 < u₀) (hu₀1 : u₀ ≤ 1) (hq : pStar ≤ q)
    (hRq : MinEarnings.Threshold.revenue D q = MinEarnings.Threshold.cost S M) :
    AbsorbsShock D S M u₀ ↔ M / q ≤ u₀ := by sorry

end MinEarnings.Shock
