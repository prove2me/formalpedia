-- Prove2me | Theorems.Thm_MinEarnings_Shock_phi_shock_gt_one
-- name    : MinEarnings.Shock.phi_shock_gt_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:42.34795+00:00
-- url     : https://prove2.me/theorems/c1b3d72d-37f2-4ca9-a049-839641e9ed83
-- title:
--   Online Appendix p. 5 — if u₀ < M/J(C(M)) and w₁ ≥ M/u₀, then M/H(R(w₁)) ≥ ϕ(M, u₀) = M/H(R(M/u₀)) > 1
-- statement:
--   Let $D$, $S$ satisfy the standing assumptions with revenue maximizer $p^*$ and crossing point $w^*$, and let $H$ be the inverse of the cost function $C(z) = zS(z)$ on $(0,\infty)$. Let $M > 0$ be the minimum earnings target, and let $q \ge p^*$ be a price with $R(q) = C(M)$; this is $q = J(C(M))$, where $J$ inverts the revenue function on its decreasing branch $[p^*,\infty)$. Let $u_0 > 0$ be a shock utilization with
--   $$u_0 < \frac{M}{q},$$
--   and let $w_1 \ge M/u_0$. Define $\phi(M,u_0) = M/H(R(M/u_0))$. Then
--   $$\frac{M}{H(R(w_1))} \;\ge\; \phi(M,u_0) \;>\; 1.$$
--
--   This is the first step of the instability direction of Theorem 2: a shock below the threshold pushes the next wage beyond $J(C(M))$, where revenue falls short of the cost of paying $M$, and the minimum earnings rule then multiplies wages by at least $\phi(M,u_0) > 1$.
--
--   **Formalization Note** $J(C(M))$ is written $q$: the statement is conditional on a price $q \ge p^*$ with $R(q) = C(M)$, which is unique because $R$ is strictly decreasing on $[p^*,\infty)$. $H$ is any function with $H(x) > 0$ and $C(H(x)) = x$ for $x > 0$. Since $M/u_0 > q \ge p^* \ge 0$, all arguments of $H$ are positive revenues.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), Online Appendix A, proof of Theorem 2, p. 5 (PDF 33), second paragraph; J defined p. 13

import Mathlib
import Definitions.Def_MinEarnings_Shock_Setting

namespace MinEarnings.Shock

theorem phi_shock_gt_one (D S H : ℝ → ℝ) (pStar wStar M u₀ q : ℝ)
    (hA : MinEarnings.Threshold.Assumptions D S pStar wStar) (hH : MinEarnings.Threshold.IsCostInverse S H) (hM : 0 < M) (hu₀ : 0 < u₀)
    (hq : pStar ≤ q) (hRq : MinEarnings.Threshold.revenue D q = MinEarnings.Threshold.cost S M) (hlt : u₀ < M / q) (w₁ : ℝ)
    (hw₁ : M / u₀ ≤ w₁) :
    M / H (MinEarnings.Threshold.revenue D (M / u₀)) ≤ M / H (MinEarnings.Threshold.revenue D w₁) ∧ 1 < M / H (MinEarnings.Threshold.revenue D (M / u₀)) := by sorry

end MinEarnings.Shock
