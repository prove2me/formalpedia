-- Prove2me | Theorems.Thm_MinEarnings_Static_limit_is_static
-- name    : MinEarnings.Static.limit_is_static
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:33.349123+00:00
-- url     : https://prove2.me/theorems/20a8de2a-b2e1-4ebf-a287-915eec31389a
-- title:
--   Proof of Theorem 3, Online Appendix p. 6 — otherwise w_t ↑ w and u_t ↓ u converge, with u ∈ (0, 1], w ≥ M/u and u = Q(w, wu)/S(wu)
-- statement:
--   Let $D$ and $S$ satisfy the regularity assumptions and let $M>0$. Consider a policy with prices equal to wages, $p_t=w_t\ge 0$, earnings $z_t$ satisfying the equilibrium condition $z_t=w_t\,u_t>0$ with $u_t=u(w_t,z_t)$, the minimum earnings rule $w_{t+1}\ge M/u_t$ for every $t$, and bounded wages. Suppose that neither of the two earlier cases occurs: for every $t$,
--   $$u_{t+1}<u_t\qquad\text{and}\qquad w_t<\frac{M}{u_t}.$$
--   Then the wages and the utilizations converge, $w_t\to w$ and $u_t\to u$, and the limits satisfy
--   $$0<u\le 1,\qquad w\ge \frac{M}{u},\qquad u=\frac{\min\{D(w),S(z)\}}{S(z)}\quad\text{with } z=w\,u.$$
--   Consequently $(p,w,z,u)=(w,w,wu,u)$ solves the static system (8).
--
--   This is the third and last case of the dynamic-to-static direction of Theorem 3.
--
--   **Formalization Note** The conclusion includes $u>0$, which Definition 4 requires ($u\in(0,1]$) and which the paper leaves implicit; it follows from $w_{t+1}u_t\ge M$ and the bound on the wages. The limit earnings $z=\lim_t w_t u_t$ of the paper is written as $w\,u$. Time is 0-based.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), Online Appendix p. 6 (PDF 34), proof of Theorem 3, first to third paragraphs

import Mathlib
import Definitions.Def_MinEarnings_Static_Setting

namespace MinEarnings.Static

theorem limit_is_static (D S : ℝ → ℝ) (M : ℝ) (hP : MinEarnings.Threshold.Primitives D S) (hM : 0 < M)
    (w z : ℕ → ℝ) (hfeas : MinEarnings.Threshold.IsFeasible w w) (heq : MinEarnings.Threshold.IsEquilibrium D S w w z)
    (hrule : MinEarnings.Threshold.MinEarningsRule D S M w w z) (hbdd : ∃ B, ∀ t, w t ≤ B)
    (hdec : ∀ t, MinEarnings.Threshold.util D S (w (t + 1)) (z (t + 1)) < MinEarnings.Threshold.util D S (w t) (z t))
    (hlow : ∀ t, w t < M / MinEarnings.Threshold.util D S (w t) (z t)) :
    ∃ wl ul : ℝ, Filter.Tendsto w Filter.atTop (nhds wl) ∧
      Filter.Tendsto (fun t => MinEarnings.Threshold.util D S (w t) (z t)) Filter.atTop (nhds ul) ∧
      0 < ul ∧ ul ≤ 1 ∧ M / ul ≤ wl ∧ ul = MinEarnings.Threshold.util D S wl (wl * ul) := by sorry

end MinEarnings.Static
