-- Prove2me | Theorems.Thm_MinEarnings_Shock_absorbing_policy_equilibrium
-- name    : MinEarnings.Shock.absorbing_policy_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:27.630854+00:00
-- url     : https://prove2.me/theorems/39b8323e-705c-4b14-af0a-7ff39b6746d2
-- title:
--   Online Appendix p. 5 — if u₀ ≥ M/J(C(M)), then at p = w = J(C(M)) and z = M: z/w = D(p)/S(z) = u(p, z)
-- statement:
--   Let $D$, $S$ satisfy the standing assumptions with revenue maximizer $p^*$ and crossing point $w^*$, let $M > 0$, and let $q \ge p^*$ satisfy $R(q) = C(M)$, i.e. $q\,D(q) = M\,S(M)$ (so $q = J(C(M))$). Let $0 < u_0 \le 1$ with
--   $$u_0 \ge \frac{M}{q}.$$
--   Then at price and wage $p = w = q$ and earnings $z = M$,
--   $$\frac{M}{q} = \frac{D(q)}{S(M)} = u(q, M), \qquad\text{hence}\qquad M = q \cdot u(q, M),$$
--   so $z = M$ satisfies the earnings equilibrium condition $z = w\,u(p,z)$ at $p = w = q$, with utilization $M/q$.
--
--   This is the key step of the sufficiency direction of Theorem 2: the constant policy $p_t = w_t = J(C(M))$, $z_t = M$ earns zero profit, has bounded wages, satisfies the minimum earnings rule with equality, and its first wage $J(C(M))$ is at least $M/u_0$.
--
--   **Formalization Note** $J(C(M))$ is written $q$. The middle equality $D(q)/S(M) = u(q, M)$ needs $D(q) \le S(M)$, i.e. $M \le q$, which follows from $M/q \le u_0 \le 1$; the hypothesis $u_0 \le 1$ is therefore essential here and is a pin (a utilization lies in $(0,1]$), not stated in the paper's Definition 3.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), Online Appendix A, proof of Theorem 2, p. 5 (PDF 33), fourth paragraph

import Mathlib
import Definitions.Def_MinEarnings_Shock_Setting

namespace MinEarnings.Shock

theorem absorbing_policy_equilibrium (D S : ℝ → ℝ) (pStar wStar M u₀ q : ℝ)
    (hA : MinEarnings.Threshold.Assumptions D S pStar wStar) (hM : 0 < M) (hu₀ : 0 < u₀) (hu₀1 : u₀ ≤ 1)
    (hq : pStar ≤ q) (hRq : MinEarnings.Threshold.revenue D q = MinEarnings.Threshold.cost S M) (hge : M / q ≤ u₀) :
    M / q = D q / S M ∧ D q / S M = MinEarnings.Threshold.util D S q M ∧ M = q * MinEarnings.Threshold.util D S q M := by sorry

end MinEarnings.Shock
