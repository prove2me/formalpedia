-- Prove2me | Theorems.Thm_FracRiccati_Radius_riemann_sum_B_52
-- name    : FracRiccati.Radius.riemann_sum_B_52
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:16.095037+00:00
-- url     : https://prove2.me/theorems/f00b22c1-be70-4306-88f4-3ae25cf4282e
-- title:
--   (B.52), p. 34 — Riemann sums of f_α(x) = (x(1−x))^(α−1) are ≥ B̃(α) = B(α, α) − 2^(1−2α) > 0 for α ∈ (1, 2]
-- statement:
--   Let $\alpha\in(1,2]$ and $f_\alpha(x)=\big(x(1-x)\big)^{\alpha-1}$ on $[0,1]$. Then for every $k\ge2$
--   $$\frac1k\sum_{\ell=1}^{k-1}f_\alpha\Big(\frac\ell k\Big)\ge\widetilde B(\alpha):=\int_0^1f_\alpha(u)\,du-\frac12f_\alpha\Big(\frac12\Big)=B(\alpha,\alpha)-2^{1-2\alpha}>0. \qquad (B.52)$$
--
--   That is: the Riemann-sum inequality holds, the integral expression equals $B(\alpha,\alpha)-2^{1-2\alpha}$, and this constant is positive. It is the constant $\widetilde B(\alpha)$ in $C_\alpha=\sqrt{2\alpha}/\widetilde B(\alpha)$ of Theorem 3.3 (b).
--
--   **Formalization Note** $\widetilde B(\alpha)$ is the definition `BTilde α = B(α,α) − 2^{1−2α}` of the constants file, with $B$ through Gamma; the statement asserts the identity with $\int_0^1f_\alpha-\tfrac12f_\alpha(\tfrac12)$ (an interval integral) and the positivity. $f_\alpha$ uses the real power of the non-negative base $x(1-x)$ on $[0,1]$.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 34, §B.2.2, (B.52)

import Mathlib
import Definitions.Def_FracRiccati_Radius_Constants

namespace FracRiccati.Radius

theorem riemann_sum_B_52 (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) :
    let f : ℝ → ℝ := fun x => (x * (1 - x)) ^ (α - 1)
    (∀ k : ℕ, 2 ≤ k → BTilde α ≤ (1 / (k : ℝ)) * ∑ ℓ ∈ Finset.Ico 1 k, f ((ℓ : ℝ) / k)) ∧
    (∫ u in (0 : ℝ)..1, f u) - 1 / 2 * f (1 / 2) = BTilde α ∧
    0 < BTilde α := by sorry

end FracRiccati.Radius
